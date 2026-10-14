-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0720
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:21:37.720763+00:00
-- url     : https://prove2.me/submissions/ac970c26-fa24-4c2d-978b-a9f4c475f5dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 129316546 ≤ n < 129496402 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 129317796 1250 129316546 129316549
    0x170c1e010807080c07020409020103090203160501020601090903021218030703030509010305130203150a150605040e0903030c040b0c0109020a09090203070602010204152609030403050c0102011b0503041b090902 92
    0x12150446218240f0300a10b240c28400d58200740103128000c1c1c80750351500c5210f030669000c0da00c028815a001780c15580d640c2c02800510341c01e40342500c10b05006103c1c1600000e0103041d64450b40310041c0c6d155020b04026000b10074400e0403504100d016041d50b08442511003181ea800f0070501c4000c40c480e03101c01d9203071040704002400702c42d0011b1810703615000a001000c01647c01160444c5203aa04580d2400161a070843c081d00600700e00b020303031260345040b0b0b50101f0302c903403c40d003e002150306d488001c04840e960424001d0b01c0b40001e55001240741c000784803d11411145101401c04800380c81d0000890003600e40020b81c5100c0b9070b50111010310b41c3c0e9030843d001d40c2010b00c441d0014200310700081d8a06460981c09003002c0c00c032061360004010a2900c505841020426541003c89054034a80c11a041600d103182c0c4170384c0f007072104031101d10503091000c0c5154010b02030543d50340310222800f0241a1610001e0396a035100810445400b0b01c0940380a03030400075005502e01170301a0710000100b0100920 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 129319046 1250 129317796 129317807
    0x40e0a0b04020405011b03090b031305010e0f28051605010318050c120c0301020d05090601080c1008040602090904030513091a060f07050a050d03051e01170c1e01 71
    0x31203000310700420042c0302030b0741c0008022241801c0844501000d60304d80c00c0480d086505500030403041100002440100102d072181411000c4c040c00c020480810a0310100b40c0e1500c03075100151442d0441d80714201d4224102c141175084802241c00102e00300c100780e940c00e0400f07035486080c41a2030400700e02884107580c0b40c0700c3c041d4401180c1841c14a690440c1d00c2e5071380c1c0d40c00303d07803481c80c40764550448428041109001404a00801500a649a8280107110000307014200c58021a510441c400015004800a000340d04a54054400c00d0a461078450803200b0310300c014800d0710301070b801704003400050312481c80d19446180170783e50302c0343c4505000c0c01c00b00a4213101e9014800c20350804400800825500011090941040380c4ca55a940d07248a040742c42402055409416405469158010302001084500c1c1e200211743c4d003084180c1c1c80741d14241e80d4051480c01d00e01c100340b00d8401802149842d4411f0f403200c50090003180c09202080b000a44041c014011042c04034880c0c600200e00303544c200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 129320296 1250 129319046 129319061
    0x60609150503090709020c01021c06030209090a0809040209010302071e1b1a130803070803040c060503010e060405070908030d0e0106121707030909060b0702030c030f0a0b0417040e0a 80
    0xa15010b4514246103a203070743e0322100f81c02240210f590018940c110b0520940c11520038034804074130003010042c890240001006144416030041090000207901c0110100d40b9002a43c0e229410f1803c222101d01808002c1d0032400700c030b80c18560308001010108031410000d040005181403520400702003450240002c91050500d4001c44810240030310410301081c000c000d020300d4000e0850b40310284000181140c030f80e2035000b11441d0000090700004d1040e08402184034601410100e042159100b004499920091203209616207144000c41c040385000e4204030b0b0800c26034a44880f0240e103a41c00b142c25a4801540d07284110745e03454404595000030700035100100f41c4039007510b001091644034082c40b90300600d08603039003c000007070708010540a1206040944188081080110385078409194164010f01042e0311900c1414121032030b80c5000602c400020a0a4014091034003203036560b101503080251040b11700c0319001f6000050740e11500c000d0801800e2401965240f420113180c0c100484114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 129321546 1250 129320296 129320339
    0x31005090717011104061e020303060f0d02040b0306010b0904050109181203060f0909061410050d020310051024050f09060d0c0e030c1f140c01060609 66
    0x400040054080c03012902908545818240c1d0b5945248296410300401c100482c1c0192541c01080100d50581d0085e10024104200500c04111500d40402660b503404106d0340d00703500840c0b0203e140e1150070030000c4540003034030141020800c036a6080000e8200b4030309800032503038500042030210482c942401600c2c010443c0450800c40c1c000080900040420106805426003c1451641034400d100381d200c2c000811070380c1b405040c81e913251020303800544001c85003694583c1c18103081084081c05017184502036030b800e049035402e00e403500d414800d00c07003c1d4440030f0707a0501500c40d2010118002e801100e10407202112400d60160070442e903090f203009140e00c440031504440c850f003401503800038212200b0f0b032036046040f81c82d090707688001100c91054010542d42c050a0011300c000340d940241c8d40d802100030440503501000c001e001071041c40d0000c00c24145420030030700d4002c0c42050040b808030750044058440c0e10326000030703500e543e030a4404a52069000030300c8641f00b00040c6102564039100200c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 129322796 1250 129321546 129321551
    0x319030f03150b0f0307050d06030c030311150a1a04150e0c030c030406051b070b0115030207050a02040906022802070506070213050709080d030b04050703140f0a0908030a0b0310 78
    0x8180c0c1d0300c1014020051882c3d504d040000c0450b0b1418010010b032138442071601c0d812703ca0b440d180d14000140c010325210880c08604c81002070414040d01051005020b00c000313201c0317a866a101c080c983c02a280d444411954038440e0343d00e03104948ca8a00481030349840066040c03144074070781a0404c100702c8004194055800782401802000150101203075001074014901103001e4076a22115014042850740d03691240e007000079407008000c0d100b0b101504a50141040c0c441841440100303800782d203e003810080c59504211580c600600d0140c0c451031003540201c0d00182482400c14520019100c0e68480710044850040c1085507aa81084030354044c100075158681064415804500110002070b1072803410350729607000900303c2d445240140c0041c120b4070110346440b025928080c00038408540700d140150f003004001807001380640182c40760001d42800201c0f46a581c4011002c841c00064031f840c03240d0b52214104800f080c98040a140500060700c000035a003150102010b20f000c0810558155190 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 129324046 1250 129322796 129322799
    0x1090212070f030813050d0303050702011a0a050405040c0515040f05030d0c060c030938010501170702030c01110c010b2407080705030a0f090806090d0e0319030f0315 73
    0x3450082e00800c990380611a00e4032122002078410303009030f040d041180c014689080500c01c0c1a455004180204900c0e000ac03c01c00f00b143c03c07036901c02c08150440c1307a00198041410402802d00e42e10041d4001e00601d040f02d0210b444800003400001c03c00348404e0a5000070078207000106000301d240c001401c04030024180c4945e0424090800d80c500e1501504d140e03659070480d8003280c000c0d0080c0440a82c00b52002c0c4e41d090780701c1d0030b83c07582188085407444440400c1034503041821200075035905854058440700c004c20700800c9030f41c0d45c060740113180d0001c50000703112500f942c02d400d0051300d0a01d8649800c07a031b120446410f016086503210781c03c4a100e034006144c00c41c22501c20501d140d152407003000d00320380d40e054a82440340051142540080142c0b100007a0208020360019154041c0c041968a01ca0000c0d51020901d945050507a02c8d80749540042e070302020303880c1c05002c22810103400034041d644525144403490b4034140c01e816058003ca11030258002d1415032600c55248651005130809512a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 129325296 1250 129324046 129324059
    0x30b09070f03060f020c06010b302214060f06010203070c060f0c021801050108011a0a0804031b030f020d0c0b01030b1b0409021e042706170109021207 66
    0x1414180b00160106982d50102680e07044590100c03000b1000d0303071040710f090f07503510b070311204003903200f00721082c03480a1400c468030010b041e68108901d500c80810080380c99866455000301d1780130880205040e4500ca04445100040030704980e00340072500d900103040e080c64402e83c45859110020203441c1190001c0222000003071880902c501640c40914020550040e110400c1d6114005894081d61050580341284410041501c4081c140c86c800e98942d855640c3ea04800b40013541d1102c14182c110341d0074071110524074880e440e0558801c3c041d28120310301d901c88041038480c1d50700e001c106800103038405887c614a41d40412501c95011610310306510001502e8403852203d0700d040c0001482e2410000200c1d00c140383c07a108200c200d1140c0c0f801240d40303e940e01d8904009501c4901201d441d808410a108209507188082c2d03000c4a01100402140300c0c400c0700002801c00700d0454205219541d4000811000d010b24025021003924000001d0b40311940d0041029042412450780b400758401107060120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 129326546 1250 129325296 129325319
    0x601082203110106050d05031903020a0c0b070e04020d052410030203090c060c0601090501060302040308251e03081323120d02040e1501020705130e06040507030b0907 73
    0xc89415207041001501800702d002d01400e12544000e03804105042c0038001e02601000500514881040350a1b4001030010300b41d0036402040c1440f404141c89003c0d10000c160030301280ba0340006140b070a0340703010700200002000c07a0400b16002d40d1482c6d48008000903000300d05401200403843c02c0450401c948403800107050107450703400750010035070044040303000d110080090114005004140c662a03841700c0c0c505c255150320910071101458100380000500310f0107842140d003600c0c1c010036203034640f242c4d03000d6400680d880070409802c5804151020b0b408140b840710000c0c80c00d00704401a2110001a003402060305001a10316007900403202180c00000e042c120f4001003488a0341240d440070607a03008540e0400701c034540c00c800310041c0098808902c051960007442500d4400c5010039054403005603411840f918142c10601680c800c120520042c54424003680d01c0100e0342ca004a00c1d8031401c90340310b0510300240d03000c40d99940b2002c014030402175440c2d040342e80003e064004028542c1b804200d01c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 129327796 1250 129326546 129326611
    0x260402090c180a1e0603020309030403060e0a150c02010b0405090601051221030f090c0f060d06080304080303070f08040309051009150e1e0a14061b0105060108 70
    0xa04007000603a4240c046281032041d0700110300800707441102d40d6a51000c0004031640442055504900d40040f0303c5a00900c240d0340118068030046003010b00f1a070b44c00c3c0042c0080c3c20303400c9852280c58030503400a014092908142070140b040421031889042c0064203440041918034071440c10941002500c1800080a504582080b01e4520009524507480e40c03c0a801c0500c07102c82d09a000d05410705201160f00440c041e504103191225a5512903d5040c3c0b00d8079581d4010758407000410300c2200c6442c120000c0c0202400c0414005485684d41c0401803959009a0240030345800100030440c1098201c02100700040050900c0030592820345e6000703240610301d0051521982c00da60510441e140f183d0025005801c02800f180324507070000e040034141d001d079011102c1c402c1c104003019001f0290303005140c11280d0b02c0a06902101404e01d10380003400f400c28000c0c0350b001801449080d107505052004400d031f00030010000251800d150740010100c40c001041c120210001c110307405030b400c040c5c907070350360 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 129329046 1250 129327796 129327811
    0x3050d0f02090603041a010b03060904060c02010b1306030209060a0b19050f030901090c0510052a010903051b060c180a0806070f17131502070b01030326040209 70
    0x301424940600c000070b0259110b400e03004007000c0704200400c6a000c6110f0b003090050004220542ea841012900724401160040c4e0084482c0001c640000d10035000210b01918500010a100c48814042030340d13030304074011090009403100010015814030854050700118203442c1036600b103043c0100000d09110303010b024211007100a205141c1d55200f1000c4d030320503031241c1c0c00c856501c1c105604c0b968040d2100150950b0203900d00c0800007418070740402d202e134000805845003800c00f6a11910620b04c0002c0c404034820121074a426252501c80a1041c4000c0c188a82c17906511880384082905801d2050000004142c0c0924240f207041c00710306083e900092401e6080c40c05003107400001c1252410340c0da0180010340f09907402c0c080c3c6590005603800c2e000c00c0550342c0091565005511408040342914204180401c2003071180100300c0c0c00310052042c01c2c036a04054078108003542e034945002426801500016010f0000e00490700d4072285800e60781c0415000014141425000a8604600032b0000c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 129330296 1250 129329046 129329051
    0x13090b10050a0e0402030c0301091a100e0f12010203090607020c15091207060e10030506090c0a02070807060c0201300b030106053607050307120f0c02070608060d03050d 74
    0x420b440d500c60680c8818507803015205540780d0a00d81700c203000b15003080c082d035000e160515843c04140f1030301c4850703507210000003095a920100c0c03a03201034902c4480c509849801a040312160070042d1641407500c801d01d6aa070000582e05d2429408207801e003000500305a086402a00b251245607481e08079100c0740d000c0810302c0d1030746d4041500000b0040e00e03020030889100c1c020f00c6800100e550700301100591400064880b000c2d40c48408070102c044980485038682d1061042c000b241c1064403803400b9180f584131074011596402d80359a801c52500c040d503071008000808080d400d20455030700500b4007a007049200ae4041d810310480360801292481c40c005552010b0783c40b498004559000d411000080201030501c101c4c518941070740e0011080c01d01e00d00e8003100e03030b40420300082c60305800c0850710403000342ea2441d007551205c0404070345078502c021080d6003654503902cbc03006800307109219401044210b900105040ea2800340050804040200740324810080031a0900100b03400c04200c504104460100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 129331546 1250 129330296 129330307
    0x809010c02041a0901090212010e0703020f18010f09030305030609041e030207090e030301030c03200a0b0306031c02030a0e12150103050c0409020d02010e011103030c13090b1005 78
    0x100ca010111203000796000c3d0510741810707216469450120703604601554100c0752aa25101e5050983c0f084500e408074100450004001d00100202d04980102c3d00b86405031030038005282504890b005914420781020804404100660300710f03a809090030407500b00082620b2941c1c0f409030090000030314050049003032200081c2000b03000032072600d840008000c202d001034010306000356200103d0003444501d0340f030110715400700300000095074101e907400040d03041c4540c1980d6030a1807441c070362607003590000401070441145a07503080701c20000e4840d4010498503460801c0c101450009441c04140b89050f00341107051340c041e4080102d4032861150700b8a4446e100e040804100001040701c005d400301e0007007080c07040340303600d04030500c5040717901590845450404043c1044100c882ea440000d6010501c4018000103500800000300144c0b41410000c02021002a800b03065500486440d800400700161518a107100f010895014240c40c00003040100600c00219103001d60020506c0107021000c0369 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 129332796 1250 129331546 129331549
    0xc0207030b0108071e050f10032a1803120e0109090f0615090602030a0e0301091202011e09020310110c01060b040303270e0601030605120d021212040809 67
    0x9888025a881210401103603543d1a00c1c0d0340f68001030180c980700c0a2600c58542c0d015400611140a03140003c205402542841d800c00100c0713450100464281602c0b00042403030803000c2c2d59040740d04004001a44e13031452282100a00c2417050000e40c10f0607120000c2c003030011500802d00d484c200e40e114100704244420220042c1d0351564140c0c890301090342880c24903007041040740c205000726000480203840c1041c19420584029945010b42e60041c2e07c244031a00d0311606c00c2c0d91044030980c01900002e51000300b5210800c0351227038110944003503912400c0083d26041c6003050b801d070440c0c002404000c0f00c15181d00003a110107202901c800344548501e901c0d08840040c0049032262a0703000002c11841c0d544c1c42811026801611081d80442c0000f040f100d0446040a60b9894050f40d0200b84000d040c01c2a00320310781010050905810966a43c00c00728003a00d030401014400d0b080000104905000048002e150801b827002d030040c0c200040c86400a46a540c070340b20390300030345e103c142d65855120070320 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 129334046 1250 129332796 129332803
    0x102070507120b060d11010503060406150e0a080703020d0b0a06050901031a0703050105012102041a13080304150c1a0c0a120209030d03020c210d050108060c030a0c02 73
    0x92020380a4040c4010024480031030708488000c5a118154881160b5034260030041a0740281d44041d05198045d0304c41c5095600c81c07001540d0200b00140009665030b140c0758103904500e40d2807681d1001c90140b104075400e0745894034820340184045401024928159400300c0c1d5922000c40c00100044d441c14003003500e607010354111401400018100e40d0403980c2d6400c14030128145417003990305801003800484c009a104e40070b1541070701c9040c1c449182c1880c000003079001203030f049107020880300c5e030a00000c19202c00721703002495401c840b20041902c2d241d1000040d80440303082c0d40007100c3c5074020041000340541000c13408030011440e080208040e01142050040c00000303a000d00b6800d0080420030540000000240162104990b50040300002480c1114100e1045091199050340145a4414010b00c00c0c0c004000c030300d0700481a01d030803040101c10440c04403110b08088409040c007042e204002d05d110310809005009080090280b420a4510840c1500c40a8505402e00d611042050310b51070003007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 129335296 1250 129334046 129334057
    0x2040b0a090509060106032f070212010e073209151011010e010908041214010501030c0e0a0212010b071a040302070501091a0d0510030f0f021008150603090102 70
    0x1941480540f820468140c0c13070f80d809000d114046841e04840c0c0303090501540514000010445901e030b590b500b020022311243e00300c1740c02240e101450a076480a4510b00307018a20b0250b2510000f4101a0300b0240228900c183c0c070310132409a0f000390740000e02c3c0c0001d11000304074825415209052551542c0651400202c2c55207001e541024040101241c242c1c1d0012814014990080007001045000d4903410300341c581e000405420100240018002c1c1d03c000d00c00c10b610f0a02c00d10380c54441d0500d124901d070a540c400d07803054448000c5140f00f000385803030094800342d120715500c3c811032901255456100c4c0484040c041d44021000200380102000100c10921441e81c40c944421000c919003440c2c000d584012030700865002481030362001595034030400100800c14500c4404a04003400411000001d200052000c00018803019001000c41c1e40e1450b803000f0180200394a5450b034001e4018000740da1614102c16003000080002c0054a02c02c1803218034140008441c81d640d0703902c5c0d00e104640a4080d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 129336546 1250 129335296 129335309
    0x203040909081b01050f040311070801110c15190c09050306040c05030c010e13020d110a02010c030b0603070f0c05160e180c010914010207030b0403051206150702040b0a 74
    0x5000e000014841444041c103038020158007241c0c1812241035a03d42a200b0036a5005e0152809101003030000c1e0003601140c410094810031101c100c0c0d500d115650940e0911140841080000258a11001401c0c448010b0915819506030350900707202403542d100403407101c0942d40c141c1d50b074061440014440d1000c50000c020050403103119051a0130401a01e11003882410b01c0b0b481200d0300040554015000340c0030801005008403140644061711718060360018010045540d501c80c0d0f140c0403d0890f5024007854510341e400000d02d03c54030710020302102c030b01a150900c261014000c01009903800302c00e07078681403024903140c22821074502d4480e10707261030150343d00a414500315010460504001c42c1c00c0c440c0e00e8140401c0e02c4002c00c0d00003030780c076494401496400038202007402d21046201c105070314950308041c81101e082d1907072515801c940c400305450440c005880050040d04c200c01d1914410340002003201c2109240c1800180d00c0494450b10400901540e1034941e030001507500c044000c2c006040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 129337796 1250 129336546 129336551
    0x10b0a0314010806191109120a020907020a12080f0c07110324010b03040b01030b040f0b0a020703030b0f03030d0c1b0b040507060503010e06060304080702100810090e1005040302030409 81
    0x3100c200355616420116841a009442c114151083c482c40d40500c3c9040080b020b04289410b10087c10b00c00030b14a500004500d5102d40720043c40142c5440d111203110384182d0340a404000c08034a4001010743c1030114103010810f2002c03d21007101c100c0d00301b89801018444105603210f43c0d920f000c2000103094404182c2c1401680301120941c00001c03180d501700da26840410049a0b202e0101102c240810f54018104154032401403002a1210079455007003800340c843d1542000e0140d5459094550842d91781e1121500815543c04141c0c00d07006e170481012045445030040120704000c03079900c1c000c0703003482c3c500701ea1142c1c92180f40c0350181c3c000c0c4400c0526085141030480e1281890b40e040030341940d080301c903807056050010700f0030303c00c0098038181d45030310b0f00300c82183d00d41c83e0400003a9040540251a01c41007082904016500ca940d01d0802e80101d0b26000700794613241c0300e40c130f00c84266584242e60882c20006208071400020898406210003c0f000051a450b1400d0803491030080e034001c40c220070b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 129339046 1250 129337796 129337799
    0xe0c04060303080105010f0318140f0316060e03030717130203030403050f1c09051504090f0c1b0b0103060c050739050319080913050a0e0312010b0a031401 68
    0x507481064a07040e217001780c075200403401ca850000c074101c40340220f0300c004c0e20040b08140000258104401181401404111040ca034064900d081c215402100c2c2e404130310003106080420060305014010b600440040031310305601d4800805010b070b100b441ca5152030101d03030400080016074400401044150060210303601d554403445c0c1030341d40385280c40404003a485140c03490800c0c010107602c66a00701e6842c0e9a45c2c0c4241d49814103010004204950080380840c0500c80481d01544c10b04c109548400c1140010a004d0150400600003520108909843c888484004000301d40d8507604541102e40c0010002140e0200ba5011101b9018000d002498040712401382c0c00c1c0c140791001130f007011040c0e02c400134840030024444135401038190f2040316050381001a20403103041c1c010020310151400381c40d11925011000000810800c40c040c0346400641e51601846881e42d4241f103100d1009a041e0000c501d00340d40c108400e02d07030401c14421680c011b8800200b0801c0c462086d048003a031001101a500c0c080e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 129340296 1250 129339046 129339053
    0xf2304150c021201051603020307030225030f020106060917030403080c03070309120c06030e010b100201020d141003020907030b041a0916050d0902150315120604020102100e0c040603 80
    0x601c8800040c0d11540411010078055078041c8a0103005054503801d20001e6080d041042c0c0103500700034400428154240312900c0c02d5a242040c1d8485d02e51040100141e0010034036001e08246500003801045a1500b40e060000ba40c00c80d00503070a503509400344a800c02c05000c0e9031882c500c199040282030f4000482c0396100701e10004050603219110b0345548102c0c40d01c540201c440c45200c2d500291011207000d80410206001c2e03440090008148000401c0e094860804103864810404610006070f40c0040d0f501c4540380203100e54204107031041d031800da507810100400c098541282c00060300c10301c80b010100b081240264408659260301400a01c50002401c030b4892644140b010b016008200200014510460883d0100e14003d40c1c1d0711a0380c208610800200c00a2002210498003e406081b040511031406406503209207040764180518405140c01e008403e581c0127060144c41e4400c00a100050384c002c250341e2420f007102c00300020003030400004a40343c05c020a11050300189494070102c20b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 129341546 1250 129340296 129340307
    0xe01031e02070b0609010603020703080a020306120601081608060903090405190e030d0f0203040201230903100204090c021b191809021e09040f020406030b010e0a06060f230415 77
    0x203084105d8a4080c4c680c0d071000c0640503442480070050000343c0140006200240c60342c0695008003001d030414a034122008040c80c030b495002c0c0c0081d00240c0c0004035080e4015920000d04021700a03000c0135000d2420800b1045680380a0102d900e4840da44540c0041e03400c0c1e25510103d40422203254060080042d29400b55440394081180f44030058144023490340c101229008407400740da81079403580658481424242d2031b8401d41c003103840d0b4a0700d0030020301821b0b590030000c003505500c8140005030f46510b0616103600300c0b25079800800c15500b16a444c0e010b43c9120032600078000c3d0f8251388450541a01042070481042250813500b000d400c10031100c015a8900c1d404421014402d07512589018821600d51281c1d491140c8c400398000d40c5100024001581d000c103441b01184060b00110b0f500752a691809c2d15041b003604920030841d41d00b020441e0301e0b00640680e4004000a052001d401c103a0307444000d082040c00301c101c554040d028a041200c100c480408c07140100240b0149902202d60228024030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 129342796 1250 129341546 129341551
    0xe0603070f030c032901020c030a0b0916060c081804020f030402041a0a0605070611042d0f0501080411040f020403170f0901110703050111030a050907060e01031e02070b 74
    0x40e103000c0400301464024441c0d1700c2c030303038080d40003a20103c0242d8030341e08410410810800d0440c000c08050100a031010816035030700c644240107001e407900d4929100341c80c211024442c080040c0300a002000100d402146074448550814010303541c40e8a014055250945030242081d001440000c0829036001e16201460295100300c80c01d10541003007039440c1e59501e01ca01400c0d548040980c0081015074014401000094440e613804105102019880c811540140c0d20102c50884e007600d01c44e9402c60070b40c004c055509034542d2252075050400d021004d50540c2801120305001c2c0c2d00c1e01140510040704608545000002c0060003061074451001010350024030046030220940d00c40065481010020740f40c0720804111130340d003009551001103d0030425802030706030602174007a000c808520203005201c1c41c00ca078900c481d40d403030801c150001c00310361005003101d806401040c410700800d54800c1c210710114109180100d19001e4002544003603000350b0210481880c4001980c00c100300c1d41482d4a0b2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 129344046 1250 129342796 129342827
    0x5371203030c0201050405031606090204090b16020a03020c0d0503070b0109020a200a02010309021816080a0c090e060402041e15170109020f3601020d140a0e060307 72
    0xc81071508807403da09843d01914000d207140c1040c003540d6850000400c02440e05030003618041038400722030300800d040703d039400d60944501352048204018018044002844410755100410003982aa10020340b20f01074060028841d504810071402802410004d403000140c0080c0004032951b5540d01d182c0017540035100180226184900c0107007480e2280c1e001802c2411401c002d0030403c00c40e540114020995000d04036401031216401c0c1001294001c141c0d80f280e13101d40d071071030385c88800000050b040410051109519030700700034000051a501c0ba914904886c84544001035903118440043c1c00b13030155401c6450902000c004403000c4041ca101c0032001c0740e50740d00c00c0e2581900751080403540600d130140045448100350004010112a640c010005214100c100b40e0502c0710b001e00030070603441000c2040c2d03808410070754101252800381548043d082c1003400200500d18611070301400c0d001040c1e000364407880e804101000384034001c242002204070b0040c03e8030303540e01d064200600341900c00342590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 129345296 1250 129344046 129344051
    0xf0a0b060607020102300a0806010806060c100e1e06010f1d0106050702040207140606040f0b0d020f040f060305030d0e01060e01050d0303110301060509040b06040537120303 76
    0x6415090550841d0b07126030301a40505021742400000d0360884102111040424158041c007001350801c2602811003414a6540c0f00c0443c200314000400c0b0100c0501854880e502c108280c0032440380c0002c6400034a00d041002003414043c4a0345542001411100300315115001000c0c65a030200218509050701c604c0886900c0036911451500c164000c01e40010305203402d6a0014031400b0b003d03c0c040d2840a200030030140c50801c003036031209405d182c03540717a10029900440500c0860300d0035005094000220315400c10051065a0000e424805014806030240144003a084190380f03598101569061040b04203021960b0f0324500203580342c0c40100352440301d070314040c402101c2c85e1044c025882142d01c210b2030251a642000100916007a03121421810301d951041c004519006106c0518020011610381c6916080514180010380f00d8040040307200340c00410042c01155102d54170818240508a2070520380c2d8403400e40c800c01c0200818403080d4034112031000184130101c0d50401101d451103503506 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 129346546 1250 129345296 129345301
    0x11040219120c052205031605100309080d1805030a08040b07020f0705091e0a020301050a0f030b0a1e0609020a030b0409020904080307050d180314041d04020604080f0a0b 74
    0x2524221504500ca000003e1020040707102d9030428541c1e81d010003078030285400c100d81d03512000a0301e411028143c0a035420a642c0b4100b040307141000303c0e08401d00c00e6050a00c490036190b40c50400600c10f82d101ca90040c3d076a6001103694900a503001c03c000b991000440f541c4a00074803000d806540304540444000c40004e0004103c588040f60911305181d142c0c0040641030b040c4410403c0300c203802007440c0083e42582880707103600000c040d0340c0c81c02540e61041c0144e60f5410081441110140344c0c00150a01105c03080070000600110354040d40301a002000040200b8030702945504500542038602c03080303040100c0030450702d21a6009001d92182c0d52820024007081070240401c1d00c142e41c0c0083d500598460000d130228501d5402154070040300d20703240b45002d1100703c0803411203d44008002c49602104051810160092038200d0006024607881d41418a40403601c42c806040c403c0381207001c0610004101152515025030b4003402c02102038406c1d6000e6007001c1079455003107650585207400d80201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 129347796 1250 129346546 129346577
    0x305031e07080405060d1e05060325180e030f09011b05100b130e07030209071b061503121205061e1c08030403050301030605090303010b120411040219 66
    0xc4940c120760290000f800c003407405040104582000400d9141070f82c0392203029070700c0c80c4c07c416201600d80d007008000905e400e100041c5452700700d040c40354a9210921229940e0524079039215075046070070180704d0b99403d2504034480006407050799001c44e1140b00c0415008008403052002e006c80c0a000ea032110b07032038800c80e8000034160081c00e0001c1c00c19040944010520010398005034440c2c4009003003a9039200c00300e45103008443c4091512600f03038200460501c118944031480303a401a03900d18210b0a0b460306502d00c050b00c00170520006000d80e030703a0040c016401c5140e510120045400c00d05040d01e05010407005020807807031051054255180c4000121107141828101c030600200444110307880c080b800600444030303500c107804000401d0210606000071020340c000c510451007a606c560b2a03514600e48103046c0c0750003510481542e0014001445612000b405581e0002c60122307180a507901c03642030000040c2c90101910303400500008010400061441902800600b5981c501481c5144005e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 129349046 1250 129347796 129347857
    0xb1501050f032d070509040f02040e06190e01090902120703121101020d0f0e060a0e0a0221060106030608190804030210120c0f0f05070309060f1404030503 68
    0x1080111024002d101080075103841d103010001c881c10200e1030089610340d41c080450200000c4400380c00045c0d00040201c094107040c0a110108214038405505240c2064800c400850005004c00d0291001008604011040c0c0c0c0240740208807031524400b203940c50301c0d5808040c0409070000d071f0207402200075007145802c001900100700da4000c030441c0780d8094001d004071207078500b0030981d401c559000e11170b0481c084014030658400a440000000b03080d9003a500301414a0340c002c10b4030f4030b82da14140d903041c2a484041034140520b80d0440350078141c0b96009211101b40703005040b0014040c8035031400403071a65050340c414001d9411602c00c6400d400003400301100c00c004030b0038000b40b0b0800c042c0310410040c1011000325032890814104480c541c040c0d2025803086403c840600c0c000100403601c601403013a08032218805006d01882c2c6689021942c0e2809007042e0a0fa102c1c503401c0001a0480350b5815202e5106100b0080c4007030300c00c0b550707543e0703c0c00e0407651703508280040b6000c50a089002c514110059 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 129350296 1250 129349046 129349057
    0x31b0b0f0105120c0f0402130f0303080c0f0316092402060c0a02030f090402040510030506040606030501030f14010b06070c030506060105031006030b03100905031b010506010903170c03070b150105 86
    0x403c010030704000c81c2c400f0f200c10005c0e2622055049a02800341d200103481d400360440103400401415242e00b403942c00c1c024981c203005070502c00006410010781104a5503501141c2d440075076150f42c518040a040c8080756041e004e0350001818568088006003100740580307031095100815401c0741c1050b02c4400301503125219008810015900c100a8805170070468800362a07070f00c800401c01420140d03150082003d08000510000000e9642c40812800b8a824861900034216a190810007581943d441c420829040100039108820b122480c0042c2c080c2500f1154295601a1000d5294221413070000340c1c0c01540d000803100c1e03001d0100021125449402941d104400803100090a0352824005400400c445009035406001e03030074000c0041140c40c0100c011192003440210760b1001d4040749900c41086010240d9501c0e4100001d002c01c9070303413001491003902d0300a6107600c0250420014005144a00d0f600c1e1550f038000400c1e480240b10700070f680c49110f130a0411810700d245284100458651140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 129351546 1250 129350296 129350329
    0x5040501090611010e0102031305160501080a18081902071202030712080c010c0509040c020c130b06090405040c0314030a0203190c020411130f0807060c031b0b0f0105 73
    0x1220010440c80307200b402c50690400d40f00d4000260703140542100c03402d9034021509451480881654282001004c1140d82440080240345c800001c1c14100000c12075040a800d5180041c0c075240d024901c0e841090000ca121540402c0e03060707450180b02d00142200301c001b02910f0160080c0500022800452802015030a9008015024240c180340d910710610340707170741015039070540144104000700c0c00911a484d010381498982c19145e100c0c0004120568802d40030120454000200036207603615001c1c0c080000301c003682004101c5422203c007040203030003101507040c0e1140c1490b0600052040561101060f24045c0d034985442480f82c03041c04c0d83d42c1c401d4081d5400180d00c108800141d15a442481103c078030b045207000010000540c0029055403028142526541c10000701c1c0444401001c1c5032500400f0340481e407007080ba2030b041e0580e8071240355103c0d100c1407045d105081001c043c414403018092020303902008140303100b035040c040300d6144d00300e440a15004104e000841d40b0319050f1252032000c070746c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 129352796 1250 129351546 129351557
    0x30e03030103020d030c1b06020606040c02010c0c02010e010e0d0f1b0305030906030604140406151e0509060a180501030203151302041d0a03030516050405010203040b0a1e0807020d05040501 83
    0x4132079804a440700d003519016251170400c00c042402c1241c3d07890041c0d0082c41e01340d004180600b09042000200c07440002400300351382c0340202c0c2e221240d40084410b0340d00307034090805103020030f4080d0041c5c80c00240f6004056004091070310000800c02180003201d00940a25016038410010202140c20341c075490002501c0340e8401d000a1546203098401150710074000b60021504080c0350113030b4500c5600c240c804a4100e074403a503000b90511005460302000304107643d100450076451103000b4185020500420f4000c55580000481c0781d10b800c40100001c0004041d601081e0030011110b100502c020b0104030302c0303030082c000750350310101071894101c5c0100d030310110404058000b642000002c08034108004000c3c2c800048002900302c0a00406072040d0180e10003040900c1c10032a01c0803011000c1d516141403000070b000130f00950368000203440556500e020540c1d0751b1a031102d02a03490404055010304008651300a14002c258003280c181e0142d0125021150f407001c0e03422082d11140594000e050000f032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 129354046 1250 129352796 129352819
    0x3040503030f040f060f05060f0a05060405060f09030703210513090b01020f0d02070501141e0d1b030204031b08030d0b0103020d0e0d0f0c120c060e0609060106030e0303010302 77
    0x244081e000c160414030070f804143c0d14050a641e11006d4070300c00d290040900f55503104001d100e0408616039250007400310390b1100f0550810f00010000c4c0140c1c021103011f0007020901c0410b80309440100c40300400e00170201c9401d1b550f40d14050070401c50440d8892030400c505000000e00b01d000c0c2045d6076220800c480500a104e0401665000904034829802d045100d5410b07880f01004003800441c440300d00681c0a080c00905007000540400003d8080a800304403c00c2410702c82424615410394a40030f07102c00d15503031550809480c0c0641109641035902c0c1c46040280603000750142d0040c400c880c0708800580f4041e8003950340e6480c48615101d84a2990000c001140c560748070742c3d0052812100c141801810440608617140880e50658452140380c0e20002041e540b140d04a071184003e1209482c0915030400144d60b0350814940440d186010300004480010070402c50740c20942c00008007000701e40031032524600c0b00c0d655440a20828001c607181800ea600c85a43c003000710303130603a90041c05010024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 129355296 1250 129354046 129354061
    0x12030509010203070b010e100e040209040206090a0f0e070f0809070306050604090b0a0207030e0306160c080405091609080d050f0706060509010b0715140411061b010608010c03020304050303 83
    0x5601020280307046000421525001a284107241c5020f0169140c81c2c00304c503d400800a000c0b403103103401602d42c51a4034410000140d07501030380960f0140d41507030300c0c0c1c2e110604900403130345400403500170ba5400c0c0603c0b0070204003283e00302000d51043c14250744620707030220f441000f0340b0ba80d0000d4800708a45c3d08068024804544642c110a400041c0a0030004601e00d15450740130f0501005d4640440b15900041c0c082d05243d441a079000d0f5500c000c8000e01480e040c400d42c4035041051000f43d41017881081901682440703034803001d07540148405002c4031124075201850110b03142a007403851012a00d003a43c049141040004d4604160685461349440c2611410903007110f41c0160400b12040f0f030720740074041480e4486103070079402019907924594545400b0718140c4404010240a5991035181c000c1e000c008080540250740c20507041041310381244032134000719070b00b88601e09075441c02c007886c20240c1c1d85071541584003104484902008001c2e01d10300d14011010707072000307a6010702103900c00d00126051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 129356546 1250 129355296 129355307
    0x6010e090a0609081c020904060e0c0412050102040302041103090d02030319020310050a0612050a050402130e0c1f0816020c0108131b03030e09010e07110a1b0f0f1203 73
    0x1802e00400116091182d0b4401c05d02c200c01c03101c084030014580108a00840f400c01d40500d40c003a1485240c80c5e036151a01c0f071001c0d00240598807032051940824100d510a001082d41190f01654014206118100c1c004001d40b110f94000d4030b000010303204501c0080b50541c800f00551340240394400c650740072160718881c800040d400140041c8560741004400050342c0c2d941081c16001885261142e05c8030b0f075a1040440100d9800401c291041800e0804020041c0d454410300341c10620f0310711001070381000500e2505d29104203003203030341d400c010045160030112000041c1950828225503520705540e4402e081c2030361000e8100c14442c050381c800815400c556019080f0958448492080c102201d002c60b19550709400840c1800310982403558010300c00d05902c200080340d1502c1c280c03000c090030f5150070b1981075600e07802007407401000101c4480c507080e03000034081801e003950000b02c5101101c055560000d00303800f0301d00c206550071291800000e1030a0900c2c1040c8226440d05000403002a07160300c0c00d880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 129357796 1250 129356546 129356561
    0x30f0901110f06100b0901090e040f17030105030c0402070f03030b0d05060c040906080c01120b04020c03033d06050a030204080d0c11010905060405060903010b030f0a0506010e090a06 80
    0x600100c1290200140e604010b031a20541c1194010300701d500303280045003114003045d0880304440e041005114000e903040020f14003190030007449502195242c1c1421625140c0e07942000b032045a80c01c0181d40c0c18960140070f1416594100c040d07813101d400242c2000101e1040d094020255448035042d8004280291b212404502c4003416035010303103119a442c90304040040741c4020001c40042428445a500b0707101f44030192000100814240e0340704000a402088500d140c030300c03003585448403440131341c9964050780ea40b501074000b103d81b03c1c10052862081e00340c0c603584158041c090071980044841d01d0f40084140000d0ba1003c040b001d40c1401821585940448080c00604d40c0030080000c0e07001d010031802e480080d007170761400f418403e24a0807224203540c1107456410410080d9060000d9542c0f04202c2c0c08644c0c00b00d81c1c840da9800700d0404680035103804154258507005c1c0c00c460070860940411304202c1e082c8180d0a6400c244e880b0344680d00750140a40d80c00c000c980c800c2e00c100e00082d002e54007204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 129359046 1250 129357796 129357799
    0x50f011e0c02030a0305030a1107030c06050c09040213090c03110304030503042306070e0a06090521030c0601090f090c120606030b090706140301120f030e0303030c040e0709030302030f09 82
    0x40c1020600d80201c4e01d0910f42d503404600042c400003c10108448034800d048010900d00c0301146482c01c5510002c010101c103402c007400459684002c1068601e040c01280c4506002801c159202c0d03078401b10340040401c4038800d00f001603040902901803103120741318001e0241d08241c0428150703240d43d00c08952030b0300002e00840310030790b41840240402002042c2c0300054954140103041d07038501900700400600b1041072190146a10a6090000d00d81200c1d20307105464084d100e400400c8503150160005003c0c0c1d0103c8640c500000845080184c40400d00c5816911040014840d903d00c0900440031a0903140c0c0c0641804031400c0140808888081d0a20030107000303600c041601a01c0e62102c440d409400d0305c0c44505540708000420006400140401502103610034190a641c0740c40002c0e0325030f410320000140040c9441e449541018042c00200d00b84003005411251a45800124060030380d005002c1d1292403840e150015001034410a01130050340d40c964051400c3c6119420780c401b10790040d45929 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 129360296 1250 129359046 129359057
    0x1609060503101e090e06090d1d060a0e030f0c010e092508011502030309070b030c0705060108031b1b01030e01180f0605070c05070302150c06040c080601050f011e 71
    0x504810f60b0b036a00c44040d4411038030194203078039040411085611343c030366158040d0406c90410034610707804100d260156400e81844206041c00b1950000c4007a00c10360000e500c80c1c004110007401c01c0d4409071460031360704160110f6400c20040d84281d940e50071880c44090014501c0f6443c1e1890b0b00303120200c69046001c5111400000c07081640b4644901c2105034110009110400100f00d271080a4984860020540c0061459820007080f42512006107016a00e00c2110000c0410102c2d464a42161001a0400161141540c441d842c0c036440341e009a0480c03518040700c26a0240000002c5100d01000150140e400f9140c201040190701404402a240d0103655843e490708041200464840800034414204c06a00c601c07117251100c116100500304804000521101000040e00001c048050b280c04946501c2400b060745d01c5480035205004000000b80107000901c81088a800400b03c241c580540c241c580581e224001c0c0880380350082085400190f103a154003040f90451a29008005050302d4071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 129361546 1250 129360296 129360299
    0xf0b07030f0c140d0801060309050c0f030c060a03061d01140d0203010e0d0203030105090108070302060d090804051e0a06030216150e06280b09180c100504080105160906050310 77
    0x707100f00d60b008000401241d401c0707102d8003800143d000c480036001d480c45040030800c090442e100e0958406d02512511b0242e030360440c10402c55a001c20000780803400090030595111074140c0020054080e0f03100380100700d010784e10a40e070f540404182c810305a030f669905035000d541e1400104002d1001d2f01c0f40503a015540c1c0c20890344518000d1040c001d1001300ca0b00199580e500d0030041c8000084140d10000300c64106130801d00060340c0d113404a4036556519100405c481c02c3c01c0c101070361284525030250390300041e42d94081d4203904407419001c954203c203e03007081720169506400e50683c40707910b4812450206804001d0002a80c00710f004e8504001c050001940d802d07040e607110f00d040d00542d10550100c540d1a801000e104801c1e41d400c1d00c050040c1c20038041002180301042541101800140c040d4a4210f80c00c54080401c101441003080005d2089622103002000940b440e0310601860710503508280014044282c00700070312038211190758609044e207182010480e41900040c146e43c00c00d5816050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 129362796 1250 129361546 129361553
    0xd03030b12030a0908160806011e12030309061803090b0714060f10090c0e010503060d1a06010906020109150c05040b0304080405040e0c0a0e0c04080a050a06060f0b07030f0c 76
    0x2800503c0310589a0768100c504000d40a40f61001507071800030f03200c2c82c004007840110404a142c5045500c009403072204d01c9c0410032003844244a6801104c0c680403000030400c01d050707251704600202405500704106005c900305010060400c010005800310703900000030403840715400002c19403a40900b440048264481c41d405061800544584510f180918140701a01c0c50743c61003400288010401041411900140a8840408a40824184a004000150359403034800c0d0f501582a8803071000403100303e40d0382c81c03402040802d131980d500140c0441004200680144502061076800c0062034003c11024410f5902501312400c0820070001c040c440041c0200c4032102442c003a074460b4540c40c1d10b450521081c80100d4070f92200e10f65590303010100241c0180c4990000741c00b510094050111035654001a0442502c1194800700491164411000034880c011440300c06851044a0a200e4a070340c59004d0181810140246c0c16030340303003c100d1400082d014601190100d076190070140200031382ca45 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 129364046 1250 129362796 129362803
    0xa020102070503030f010e090706090509041a0403030c03180b0109090501090b010e07170105090402012a060501031703014406040302011508030d02030c0409020f0d0b010507020d03030b12 82
    0x250b00c1c0800c017a05500600c00341c0c4c403101c080c2c1d910068110090000900d4443d006200c00200e10480d4001d4001c4408641480406940400000d4243c000c3c2c0d6090300f0700307207001002071100c0b10400d000640340504074000d0f4492981000e581d540c0201c90095980d0808400b40000c00c5041c1c404c0360740359030300d6101500003005094602d0003094001c45100c03952400050141503c0f50303e04640c41d082c4101801444a90b4614044940058080c42c00d8070fa10960000070111040d0204094030800340b0303941c6403004002d501d4002d60305803071058456050031980d941009510340820b0141302d00501150843d0000c0081d8041c000107200c15020b80070008000e400124800c107a484501070702943c1005d01008245502405103d20680c3d202d122550440d19020b1ba0030340300d0096400e0302c08010380010202c0d01010505055401508948404564500f540441134180b94800d815103a211418105202075a601030030903140881d40180c8160741d0000306542c110010951142d9280e40b1400c2c1e14840b640d13070f02081 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 129365296 1250 129364046 129364051
    0x130603060606020a03030b04090f0b070c0c08070303090905040f0f0503040f0e0a140606030a0f0e06070519020a0809090903160c0503072909030307150633050a02010207050303 77
    0xa4000e402c840c0d80318140282541c2c1050065405607050060500000360300d590b8ae4120503803c010025915200d59900301c0381c0041c1c41402501e0349030007034000300d01c18030081000d004991003903c404450300d0b40e9070f4686003640c808460181c4201c0b80a0f0658002c11150742002c96030502c10310030340b4a803035140d6001c05c44900d20b68207c500c84012a070f082003003107070b0284290f060110040044003203c0c43c0840008505100061804621a854100d500714518560f0031440328003840c4425103c441c604018000c2c166001040640e642c000c54110484015001180102102c0d0300030414034605241d031070600c0a40000500802900e200c20040f0701082c60381c080107070381c12034800c3c00c80500c542c2c900800c06141075140c1c3c11420b41c5100f11291003020003140d8440914142c0e0244180b9201e204040005e030441c011040043c040d0480040030400c041d42c0d43d44800240c4c3c0030380e0412035a5000746039a00c888000d60040c0070400300c0450701c07004021400f410191402c140d9908c005880c1c034444e0b90300c007070035908103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 129366546 1250 129365296 129365309
    0x5070b041d0a0209030703060c051e21070c0f020f1e040606171503010608070803040e013213060803070b0601050f030a0b0f090106050a09080c0a051306030606 70
    0x240d62060526080303110090b504040b50341401d50501001c003000035200e94213484020000c40d5924100c00c85d0368040d00545d5164410029440da003495500c0d0042e00c7c5901c05000010204080c0640c55443c845a01409005070030941d00c6038100c1c45150b540c01c8d60852100c80a03030340884000c0d200345003a80c0301c01100c2c2d890004804100802c1090300306000941c0e6980e00b1a80c24085d24466680c03c1d02148007038030750700203580c00d00c0c50302c00d07445003022038018a029040b0540c580a100008242240008001c00032241021952881680c0e070300e86034403181d62042084862041c48845004100803112102d00003510002e148442000064070007108440c960340c40362905804c08500b0700c080c8081d540038554006000e080c0145000010760181010384001403000030310306d56905220140d0780b11b86800e07525250010b0070342440d5584a290150843c1c00c840310710000151a9030b001b00721200c0115124100c42030107060724240754207000801645540c14003182c020a070365510300001042a034010075000340b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 129367796 1250 129366546 129366569
    0x71202011718010c0503130201180308030414070509070c0210120e010906050c0a0c082104030e0f191413020f0c2b08071101050103060c0f0810060c05070b04 69
    0xb540450075007920303282044001404001d00c10068801d00e51804c40b030383e50341d09180c0800c0c400e05650091515000640000d45441c00100800c400c012100c18810a80200c0400701c8180941d68010841c0c401003c45403c800120514803080040c101000001c00910341424460910500143c451045070200d210b485040d0f07440d007100d5070901c103103032140d2500f00d40c88844d20b80c83c0010504001c0c04140000340018051400094841103d10800503d1140442d100250030340608007418020154640601010b110340745d9071740d2140e991302d0130550104440390840000000079190254404412210718500b54000c09515140c030300d04040c0717200414484000c0c18049403190301c40005c4604d85070324281c0c00030304440d0071010304802000360012224850064604211151344225003119400c040d00034040d681d6090400100c1040f01c04d4105030103411007030741c85440200f10341c0782c02c071030702e40096845650307100b4450400d104032403040461045040c00766046550440c1d98880101e450b91096002c016401c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 129369046 1250 129367796 129367831
    0x209070206160206010b04051c1a0406050105041a090702012007060c092304021b010501060305091203011205070b0c010e010f090203030913060906080a050d110712020117 75
    0xc42104240351610b000d00c0206030325030419895440610541c080c9520610b0300d1031920017500410501d40c2e020603400345480032606080007581c541c0700806d40d000c8503807606200010426050a20408401b0480c8035440080900c200c0180701e022100034001d603086549648008140d102e07584030501d00c03807480e00038003030351380c05541008400c43e5110300c981d504120306c50804200010000016032a16030485005410f8076807000001360013445081d04503c0e04250080128041d02c00c10f610030360488100752010b1011b941c0d641140b64070744069001580408206000500241c2a00d000100d01c0903c100200c5804a454003040c2090f41c025150b00700e102d030f442c0d8842015144080c000c880102510322410300c080481c89e8002030300d0b070040240250140e40c001020f040c0800d03940c0c00050003043c00e0f0380c0401c1440c0d00c5000c0705488024160056505200303203100682103d101e031342d82405204c120805041681d0800e440d0b4503005480c44d05c01c0c0c0c1000a010352a80e581c0d00c510b140c19003d00b180c982d1a0b04040e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 129370296 1250 129369046 129369061
    0x9060b0706050a05090d050d02090907031d0118060e120f070309060c020a090f09120e0315010302060306060a0e0a060807021c020c061608030a0207020111060903040e06010c0209070206 81
    0xd850041c25000001e09041c1400760300d901c000b503c030165800d2410070030f031203202c6419140e0003401075950782cac0c1c1d000c46807405022060b50964030682e500c0540d080440c0040d240a03001500340e0b60143c080f0000c1065001e00c81c00410103640c030030445011a0429601c64a488810250311504221170204000f08001524030070960820328074001040d4030b04040c941c0c001c1039000201e1034845e91040400b1241c17201d01c0b08400060301d80c45940000e40c003c2041070902d14401c4014081440440720324000c0c4100103202d028600c00b194018105d0f07a004210701d2450f40d404050041c0c40d0440798401c070610a82030200b140c2c43d035403400c400f005420250344950191800303d000034581035200004111031385005066500140c3d0228110700042810340342156074840c1003030b4100f49280c4400340a41880c5000c000d10240600907002040c2d41d60003682d42104402008030764903101c0e401034810541c0c83c0c0c002c1004109070144004203540c004814100307070f0702510b21900411048882201c406005800400030001c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 129371546 1250 129370296 129370301
    0x61803010903200606010503160e1002061b090d060c050f0301030b0601031b120507090503012301150c0303050403141201050111070e0408070c03080a030609060b0c0c011809060b0706 80
    0x2120f05180c000d00440c05d2000c0007804074400680f0f00b05084266514141c00c4030701480703982d0461503000e0404400b4140c0114000c0d12403409480182e070100c0400717140711400c072940c0c0036141685c0e0010200b101e042400c2c3d0fa444000c10420100700180300003804a00e285540100296000b54007440c120700e202e180400005003228007080021606407600244140c41c140c3c084071380300d0311581e0310100081c0c54603001415280301d00e25a00c015419801d0075503084142c0c103030b2110000e0600440e03070700010a90b292810402c10945601c0d004000468650050340403e1080c0c2090783c100d4042d0401846440540f9044600381c1e1002810022905a42c2e004000c50359224002c98501d01c40c00001d86070442c10100860301149026001802410340800c1c508140030005500d82c000799809030328581d480721801006009080d49114080c84a0310b00107001801460f003d00b190b88600c080d40c040c042070400071006442e6130980403030300700980c507002801103a65401c030310580300500840c1d503449403100380c2403800409 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 129372796 1250 129371546 129371597
    0x601120203010c0309150c03060b0a0513080c0108160903020a080a05100513020607020f03060f04140303010303050a1d030609070905160504050d1110050d0c1706061803010903 77
    0x2c00d840c1000520100380d07100c00c006c941c1207030a1004280018000c0d4110050301aa40005900d03000c00561203500540010003000c200c0310801101c0446a42d694015840c0c01401c8091404500c0140000704c12008622488810300d0315802d0000e04031361203070040b50300c120154100000c40d502c40d13544103060103010460484a0901c0000501c8245020381d0145c0640d4008400203010701c4012406404650301e03004149100c120107000c6400d603280511103151030340001e49094624500e03065108030309820120869050702c0c0c050f21010301d40745d004134046604100032104002d030a5036285221080c1d17a424440207010f80081001000128245041079003101c601401100c0f25020781b070303020100e10f5041070070b4030b04481040310700003558443c60500c3d00242d80200340b626408a1440a0303042c81c2e40d000070246c0b644081c0740030204050004070200340c41400441008041200c844c10000301c3d503242c050002d2006031441c0340315590451607a400319003914000305040b00802d000a59042c1e80d440b15985e240f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 129374046 1250 129372796 129372821
    0x21080702100c120c170907051512060108041b06030f1a090f0705070c0303080403170405060f09070b030c18181306091220070609050d14060112020301 66
    0x400084194005043d20254590030fa2049072151072216040b0b01030f1400000810880458200c0d600d004040c6640f01c045038082c40b845220000100d181d1320611400760b0360120380c05100401c054071214015a81c648004004943c0d0740000c06007a01076030032030a8204c0003891103407004074100c00810b2441044d1a03070840c00d0032154080f0328818071076070786600e8040d400613241002d0211946401e01c1c00c8074a8880d1000c041c0800f14910740000030584d21407003461049009648498003c0d1005441412060041d540a06142d020001240c007100d52030380c4040d040240b0404503803243d0343e02d9200039a0b60f0001c8032a4000580080b4140302010446122200e4841040b01d240d200341e080d41050122011003d08420f5106c0d4418108408000d4540e02258800350080300741490314600d80d100608020850305105140c66034900401100c05001034071034240e4a03140c40d40d0503994102400d105a40340c0e813807825681c00d014600303403162004050008501a01c2c0b80361034181d81c02d240380185401e4461040004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 129375296 1250 129374046 129374051
    0x22080d09111903060b04090507080706120209031e16030303140105101706010302070213020d0b10020a03030b190b21070e12011104060302040807090504110d2108070210 74
    0xc040b103899049400040d07980c454000101e50b00341c0801302d03009007200c200c000d11510840e070021640da4400180301c012140540c5e01d040b141802c81808806034080c203600282c1580c044004040301a05600d1a94000c559004c2210804c2c5c5e13036405065400c0340e465000364046640c805002108120341c1e0941405444151500d41000040440c000c041030707800840300003440442400310b09a07a110f0703012910159001446290f91b03503082100040258400131484070707244e20301090030070141042045500e4409058001d4800e03418981c038254054007003d180298815825078581311407030034440c84900603008141005464404140204071140c03c0a03000850f9541c55008000c5255030081c0903505034131050b10105541700456031568054040116101c204020104d004900c40b545640034200f25a101000c840e5415510307096241156416a000f5140c0707220a400e02003241882e100d00c0140a00c10426101796003c039111040d2103000c4c01d01160300280074103041c03140441c0d0400802d1b00202c507a1404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 129376546 1250 129375296 129375319
    0x60507050a06050a2c030919050904110301051f1a1207030e0d03060f060f120e0d021b060904150902030906070305060f010c3c120206010b0322080d0911 67
    0x5c07541d2400703185a918411001d440394440201e2081000300001c18001d89480d1050910b46800749085502542d0789001c0c0d840c180003c0c3d10090244c08a140c2000c00401c0340000a09040c402c44206034525a075413101207082040844c0c010002102c10300c2040ca5a40c0018492105081c1d039040c810340d40c2c8400308043c1011010310440d68059005002c8540500b059006104489030544464205100e00a103c51402c051100803c401107207000a4000300d9080d07849004502d200c0a003e030b243c00f0145a0030103010b001e5064a41003a500110b004080050302c1010241d81e20b10707210590b84112a0407525401c19014004c00c1d5805000d01ea800c680100c0f40c200c1c040c1d40c8000000c090030185103020303000d2400a1040070b41c2840100030f18200009205620f107410075500a100207040c1d0038442221810f0b000c05528ac0f8807480420454107950480f038507030b840e50316a6030561240c1c40c0c040d441c0100601c0100701c4080094444d01c0285641a10400c010602c1011410003240140c214021140940903c506 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 129377796 1250 129376546 129376631
    0x7090611010e1606180312030902120a051c050a050306040203040c0e0103050102040326030402040510051005040806011409011403120703031a0301060501020c092707080111040b04060507050a06050a 87
    0x3c040445186488d000952101c40d000090003184004400074180c0a03029280d030030701c6000f2444501c651036441240d822452485412500c41c4500d840f65800140b0500c00326000d490a0340003140c100e402039007858170b00c1c0c1d16000191803400081c1d00488441e03500050810403c90040075454041107210205101990b202411141620000348024811b603034500020350a02d43c2546004007408016021080c5401c52100140603503000703020b600524405c581c00082c120682804450400310003618042070f69181c5103407583c00b01031041029a040c019810b10100f4414901d01800b100c902955002c203080300c83e84100e803400080c2650180c0641d05102080c41707140d8001500c0c61300c0d520103a8003000c09581d003007081703165040030304010784c14606400b40300408080c0c00521241514072800c000c102c0d5170841519241c16124034400d102402d40c05010403c1a18040c502801486002e00c059a11908031039035460110342d404c80d500008a0740e110b8180e0300d800705159800c0600e0342c4500901c000c0100d5400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 129379046 1250 129377796 129377813
    0x604050d0f1502040503010f06050a0509040303110a030b18070207140613030605070815090103200306070906090e060d0803040312020d0b09070807090611010e16061803 74
    0x1446000c0d00a8600e03050820480010488400d03820000c03510340741c0c01c0c0580d65030280d03101e4403801c1d201c3d42c200fa1954255551900ca00310880b030b0010084814148cc100a100d40284010b20580506036501112018100d00c00028038070100d01da070340001c0b419128802c00c0750b900c45080c200d090b0340040600708400d064000807040203030344101c04290300c4c5803001c10006000d4404c0104d4903811500031480001040070580055000e90060f0316021a580c1c3e4840c88074840030703604e60609603c50300640040001c501e90000c01d80d4184001c12005101410381c40c042480d0a0055850b9400505145004c0050b10740c40300860b0040c0003a12030b180503a0038072100103100552031a10103030041c2c80c0000030808150140d002e0b03a0008075004010345d207441182c440c00002703200c00c915441c011401180042d00451141181601c150515150341d65101d0818030112203510b03500b4515007096580740311500207441c2c1008180b140c07a401100d50901d82c2d040400090003001c0880d0005500e0b5500d5005000041c03020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 129380296 1250 129379046 129379049
    0x6010e070314220f11090c160b10030b0702060a0c050405030604080901111002040305071401081609080a0516060819020309120c0105101502070501140408010510080c010504050604 79
    0x701d08190030711880c4540c0c0034201200403000b8004c0361400001401c10050210040341000203c440410507615000c2c0d03d0210310480604441400c0d040140d0380000e40c4c40c84d1a00d8200b200c83c03060700d880f10b841e036a030000394000540d5090056800b90b02040408940e034058003402003000d2074503a0520b441c007000b00382e0b41d100142006104240100f01039242c2e074881c1c41c000d940102880308548901d10100d111800039440b50001395010b001d207010106401c41142c04910508006a550f00400d941d41c00703543c01000301890051040003000030b4005000c0c00100302c400e40d40e90207480030344100030f00c0711364210040419911501c140502ca00c1049100d00084503450000620a0742c0035980b50340300307440315007440241c103850070250f44080303036003001203405500142c410380c00780030350303640761600c80300e450350b8001d40e0700040001640a124103020552042d513901060f50308100c100c40c10580c80700c00e843d00307480086440340303010040680e013000f000008000c1c54062090a003081440c1c80c0c200000304c0d00b5882603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 129381546 1250 129380296 129380311
    0x40219060e060f0706020f1309020412020d060b03071d160207050108041e0c15020705060d090f080703050307180b03011403030c010c031b030b030c0f01140c06010e070314 75
    0x3c581036210076080001c0f1040983e000c0011551000400740f0b07001c09401149591400c01c5020340007040c441c800344216802d03110050410ba45000360785e420030045000c1c6503000c030381a07074031007079803007540d403003c00048014000e10107141c104115001041416402e004218034144000e400384e0b15559500450090162002072918007d0750380d80c0d0030b01c00748131442c1416800300100b07204038480c1131041101e0441c0648011a0040f00001a03660301240d840d091405250342c00078040100d00300d00746141e40000d18142c031a0b8481c24802c1415110008140c11014080c0c0205100204202c40c880e40180700030380940c40c603188940d4060a00c4040ca90034003050255025900b07000444400300d903401c009462209400d00300a005070074209070000c02612110300c002011071281ea2190f11642d0180c02540302e007034000307001000d00d01088010410009004160541480100b0601c1005c03040c1d900300074072000741e602005002551503c00e80aa0741c000003404002054580b00d00911441038500046410201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 129382796 1250 129381546 129381559
    0x306090412020307050d0801150f0206150d1a100506040305032a0d0903030801060219080d1e0b0112020f090405070e0402040f0f0603090c0905101508040219060e 71
    0x50220706038514450344001a2140c0310313600302e0007901c940c0400c00606849800e40c4485030041240401d03110181100c1403080941c02080002da115810b07950b503d03142c0c00340101110300c1001a51030342014449184030000140d209002000704403500010800010700003600c40615103887c684070180c0324061445804001c880040c00b0040c0d004181030b071030354580881000d64011403514a400782074601103100442c04114480000181540003141c000500303041d0810302e40c4600120f80d110303080c42e440007004140759030b5a002000c00c000c1d16040400c002c03014074040062443c02c3e4000150640c1402120b800f88035004000355106c5815980c191000b055056402080c907845a107016550200c0c0c0c00030441c3c00510201e00000c20103081442c1c00c0440351804404107820f510f0307040c214291916043d02030041c20000304100112101c9a02c02d99000f1100c50ba009403854074ac0070b02c1c41c01c0c640381c0c1741c032500090024000d00080d850071500001c0c01e00c2165a10300c41a0b881d0080207403020640b020040c0c071070403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 129384046 1250 129382796 129382823
    0x804030b09010207020402160b150a050d0615061106010806040c0b03070e1509010e03030a0203071509020303070f060b0414070c061d06010e0a020309060a0b01021f020901110303060904 81
    0x8030940507984e000c1e50080c02076480e0011410320505111122900391502607158012444580600000556000000c3e1992035041c3c10082402554080720008030741d103da03101002c440c407c1a01031803101070103441d56121100c01b0041540d91038980180c00140c070a40040052100060018234003001320342c00d2009281e220340d9218800d45d6442500d41039942c1041003000000703801401c80c00100f075903900988404424040032024140e480c0100710030040907030b1040049101045040100c00d0020b0781e051404240c5110039401b20703065400c81a01150b5207117a0751620000c00005d401003480404c000d590030820f40b004070600d880e007580051b14107414040056095010700c100c64025504a242c00b19450701d0305000f200b0015907407602403181c0340e03040b4186408030f0034502881c000c490150101e28000c11450b11002c043c4402080104000707419840f4900300c07482d40c8000e903070710800e6a000d01c100040c0ca40103884005805000c50b0034001e42280c0040003040603503900d0b6001107403c00d41141d0300c01d8240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 129385296 1250 129384046 129384061
    0x1020405011d03100501030311070b34050f03030403031a0a0911040b070c0e090303042a17010b010e0102070608040b040f021201060519062003040b0c0105090f06040804030b 76
    0x400300c0c1200300075805c0c60004024103030005056142c110b462822124001d9030b90b040f02d04940581c00b2208003481d180ca020f15038074405556440c0c00b88800e004814807048940d0b81d4a45031540300ea40e19001ca41010081206040c0c05100d00010a4543d0761900c8030746038184006107400e00349010310040c4603030b07911856505200b0784041d20003928101c5402666250340d0300304419000c10502c80d03001c5081c05100042c00c1d00780040141d901403603001e407c140b0800d209041003040107002841c000c000200043d00014403220400220907986807103c00000c0c00001100010103a080654206065610400d0f00700403280c1e0042806a020750810070308600c540300e602c0e00c0a05008041e20195015851614480603624103510030f00880d6412034485005111015034010700c12214807178030011403c280381204a1110300f40c01d0000f00281c1c201901d1400d80c4414040800f90040c41c3d02c000180e6554040000d0b101041051444601e8000010016480c042c2d2f244405031142c1c1c0070041102b04540003040c0390 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 129386546 1250 129385296 129385303
    0x8010303200f07080307060506030c130209010e0402030a0f0b06130621020714070609050607030e010201090c09090b010902040e241f0e040515010c020a0f0b04080f01020405011d03 79
    0x500c201c2c0a450400c2da40b02d04c01170307603a00000c4091322202c0c07a00c0007050302407600249025001101500070500c00f0a40350040c002908483c43c4107060048600681c030403583e40d0302c01980b0a5450300e0000820b2041400000103c1e0880c100542c0103074000c1040a058800c17415100d4103c171524039040c0c030001c2c03407a03007a480410049001001e19600100f5850100640c0000c05601c41010300d0031103049956828088a00e22118840c250300321504202660119108031552052001c0600020507a400140d56095445000354441050035507070381410410171078960b4506004215441095041504011f03a00ea076042002d0003e105036503403040720940010751111070041140c0c0040612a0f100641c8900b1000314032510072200009200d0840c075032252500f846418012030380803160f1407081241030019030748040c000c401a81c0c02542c0305000504041e000803010f000e822818401c507181c525150019141510003640d200307140c1d0040c40280640d980c0181441555008449a89165000400480e04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 129387796 1250 129386546 129386563
    0x1005031f030b130308090604080f071a0c0316030510050118030f0602030105151806090d0807050c0f01021504020d020a0b0a020d0e010215010504020706060b04140906010801030320 79
    0x15a00c902c02001011440c6a100c0c1e4011400fa80380e03003000390f03107480390280c030785100f1640201900c030f0a00060301c03101c3c114009070a07100e1240703c14050007040100020304002080307403c00040400002000340d100d8468016000d00c0d0380c0c2c0d080c01c0c045400d15101c1d48a000b0340d10300501e4104015240c5038040840095002c07402145c1140903800981201e04012000c0c1d03000740551401f5501030702030840c0848130501120a8081020007004a8801100800445a11490342c00307134040242081e40e00442c4804000f400c0e000c5c0b150300145042c00038030302442140310303250201c2410354000384440010700884200c207550190b81110100d100b440140300184032100e0b50340200c014080f01240300c40410740c00046090204420b0740355042107840800c01240d85442c5107041032041d424030300041201d410241c01401c0190300c5001c004c0740260710b49001403410b810170342c41815203c2d002e00d2002d11500340b030410784d90040000e10f0440c0c459030454601034209200d04143e000140c400d1f545484070348034107008102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 129389046 1250 129387796 129387803
    0x60e010504050f0402190519050c0307060509030c0f0a02040b0a08070e1e010603090308091c0309050703020d0c06080121021e0306070203070219050d031103040e0406050a0b1005031f03 81
    0x1c0c840030002c0e06c010043e4010742c0c03682c2550040c0d0050801401d00660559543c541c40500a40c0b4151143d0f4402d0b01800d00503000d0a410301c0700780115540214180a402d140e48020f80c024052050a401000309440800c0045400703881e01440500840b031010500300203461080000140a40751849038081000050300488611031482c40085000f42d413580100d00c26034003c0d9550300741078840803102d980311040d0250286840146000f0050011f000340c2210518900840075540c00c03075520780102d00518000e8100700c0d5101d4400d002801040d030841022809002d11008041c0745500040071030102c031080c06400303441189520041003404e500303a09940b266010244c155429070402c0e00c0c02940d241c1005030128401c40b50071420031800c80c242e02d43d01046450040000759658519202980e044109030301080b95030100300b00200b10000b001015a0289201d903d000607180f4004100a0490785c540703c0492041c1c500c4405240c40507485400d072600540c00100004407514a003a1841181e21540d0004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 129390296 1250 129389046 129389077
    0x10e010522030f061b02060703180204110a090b0705030403080706021b010606030e0a210903060c050a14120105040f060f03060c020c0909070e0406020c0f010c09060e010504050f0402 80
    0x110030010394400b04510f0714032504040c802154040343c468415400c4456000060b80074800243c01075201350010b00d00101c00452404032050b01e0b030041001c1e1609405203600301c01c0b0004282200540c03040d141c10060900030403080c1001480d40d100c03038607482180710107040110003190180510945034102d5601c081c1c01281100a0070008080c9400b9200a1080d1004245001070100d0703200001b29102200f16403048001030b0100040d5840c0312210302c103104940c100240c26001100040720380c814500d401e031755500d90580720710b410440100342210710201d000d04407806220688030001b5102102c0e0545200b280c0106800005a131454000c1c4040e91140d00304603110718001050042076401100314401c40e0342580e006215200c02c0c000c00a5042d1107081c070a5004800800540f02c0924a040d00700c0c0c41410054034000b40880003615050251404a1090f552810400101074214802000070010781c00c5c840c20507140000042d040d03006510070940101c40c070140108955035a0b50482e115295080e0340c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 129391546 1250 129390296 129390299
    0x506060a12031d100c0c09020405330a02152820210a0203040302030d0507021c08061e0307050f04060b041e0602010b06071b030b0108030c0106050a05010e010522 71
    0x100386030b448074003c0c4c6c2d01e80c0705504041900b400758000c990503150302504124100350700c00c4604aa4201010b1021985050380c07546120140c1103400130100c60081e64010100164881d01c2c0c0c0d11054070280c440c40000b90b2520002d0b404d0a40102e0f0f480c0840591000003030129460094400b040700824940b01803c000002d04800340d40380c2c5281d95039800c4064034040c03455990360078004202e102c01d9074080d0140c0e00910140c0c5e140901da03003000768400c0461040d2146440201982441c4400d000428404035260504000e05810800d000b8000303518115130020a09090070042038507a00240034050203465904003030717196500d41c1d8102e00010007029003000c0d60b0b182d0394041e802c80486003a400808e4021505000038100d4814040c0441030900201407a282840d80d6442c020515030011208540120500000010480440704140200234040144d0382e034103050042107003100c10a4010030310400c0060300500142e40d11102a0400880a00741180c2e6805240240c00d0002160b42000c462032400210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 129392796 1250 129391546 129391579
    0x8040515090706120e072303100204050f010206060f151201140a06080709120609060504050309030106121101200a060911040c12020a2003070506060a12031d 69
    0x1200b0045400c5641e580000d030840491000c2583d9540b10964881d42c000001405443c0420a415018800014542c024031424901013070600b124240d03101d0341c0e1030b40824100108d00b07000c08030f802092000d1000e031034240b80c03001c002259807042e841800d0041801031600302050400c007085480f0100e480005c445990395032110f005185140ca0724981c001c903844100041d07a03900850009014080e603884442200d410000620301c6008401010345104cd103608400300843e07500d1140c1d50080b40954080c41d42c1e445508203040c01d507249c50b0300080b48480e84107691008980f68900e00345110000b440c0481145c0f4401460000b421502c0081700950302400a042c01000030320741c8404016031040c403031050398040300e01c200011108407a10351f1000c1040043d4201010768580c0c028800c0da242410030410b2280c1801c0f98002413031034001550480e900c005018400d100040060584c8a4412070706a80e0a43c00d1004000408462141c000c0c207003c581b80e0825000b4042000103a07241e00090103d9140055215 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 129394046 1250 129392796 129392803
    0x61e091e050108010b0a080703030509360109051005012003040806090303060405011d040f080c120301031103010203010303050711030a0b160906031107110f061908010803090a060804051509 83
    0x10156201b0681000001460f00c80030554000b01c0c0e8260303c0382420440c0c50010702840308601103280c541004400000701d144510513001d40039040d501c0110142c1e03581405100c3c822108081d021140766071221008000f41d030f0f03200304200c0141581001107074182100707480c40c42c618004c0360003852442c0075240801294001c000042c41c420701c0121014015a42d9a801111a600070042c1c14529220389800140114180035081c4244920440d001803604900c848641e080848002041c11080000070041060000e40003003400b92080840c021851035146031f8018200b480350a000401107d039440400e05180e13020710002d000c054212200c0d844a241400c41b440f54201c8841000011074421320300070030803a2291040003112982c0034045440c000d055222401031980000c120391340503540502190b0075446007000360200003090703442941540e004500240c00d0f5801600910944e520078001020595141800360044031814280504181c0340c0341046400c1ca030306900d14002000e0840c00740080c031a03001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 129395296 1250 129394046 129394061
    0x1815051206091009171303210e0f090414070306021809090703030f050f0409110415030b06030c0309030d11040501030e070e0c091201060303030f061e091e05010801 72
    0x4200b943c211030320105082044404401c1301800c46151030101e2141c40402500406501c030021001c615140d0742c80e1b541c10b012101079503140c01030028a045c50440c050300b00300c828840760412100702c2d000c58070900201b543c1141c0280058a0700000d000d000e0701d441c2c0240f044030041c541010040d503486608881c7c0780041e6118000842c059001800050303402c92001c6040b40640b03a056a40e08100c0e80001c100322000e030852260065000d030304202c00a00742d2044d1140d80c0500014140081d129442d10042e80c0a500340071002000b1705040030b00311045540c07440d04890344155209100b075207948038000e045140d400b88514a080706031508242004400b1241c001d0001c0315070903641480b1031440c80741d4241e21100507100c1e0381d40303000f19640030600320b11000c00a08668000a481030709680d103129041d41c02c1d95041ea00036408030340c0c0c654280400d803015010b10000f60020000c0c04203100d140f4150840c480000344145500195160000c1040700001d4041d1814907850300000d202a586a0785003034000d0658 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 129396546 1250 129395296 129395311
    0x204060903020a05031c03240e04020a0b031005190806250516080a020c031006060206070503090d030504111201050a0e0a03080a05150d030f020708071815051206 71
    0xc80f10005200d02d8000b0b21200340c030680164589071826031301c034150041c20b828105030407000e00b286001c0e146405021219402816024854540c504081c01400325807070312500302e007242c42c104000308840c4210300a020400c460065413980b42c40060b0304010b02089520b500542d40a000e50801d01c000080d1400100c1a0031124020242100005003402c2d00c0078030924861b040002c22806100000c28108c801519004110740141d59800c05000006400c001c014402c40c001c5035074500c414402d559040014940c81116400c200c4e20354200740d11010303940c0c08a800d0a07010140c03140c2c001000c012221102150602001d0003004002c0341545c01035001e0f0000f1291105028644500c2090018000521054684d015104c0b140182c03900e524481c0038100003851078003001040f43c80000b0507242c605103010101d0280e45c501e0080d0001d41c100a05009080d801206264415041400070045151051400c0c1011020005115850b4a214220802283d002d1944800c20241d1a80c10aa002c6035091148a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 129397796 1250 129396546 129396559
    0x40201030c300b0301051303020c011d0d06110c0f1c0c02090c0408030327060105060423060d0c0f080103050d120b030a050123040519021201020406090302 68
    0x39018022195040801126600e00c0380121020b00300c04004181140c94400000c1e021500c00303101804242500c00668824080caa08204040107143c0d05000841c04224246004400c000072400288510420740e20302d20322414580c003104040003000e40c84420312550078544a91a10440c1906030380310741c03012202e07488500903150103a6008550300c00c15203504840e074540d6000755a503074081c412102c400a0a20000101c10000458001010000346224002c0f5905081388414203020b10344005d1031011880b46994031510060100e540e0b181d05450642d07480a1141c610109111008140120005011501b0038400602400080d429403c8607001f079000d03846c0c0d55010b101c08003003203c00d25424800507065400200a030702e54540706030380c5201411085680400e05100c00d4000030b08091103e003044034943c0d5100d800707058a42030114040b6064480d008880080e00c3d02b42c590715200c000e04092803000006c44421b8104640d20a4000140072003d00c0c021500d07aa1100750203000501c00f80400d070b1180f034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 129399046 1250 129397796 129397811
    0x20115060504150305010b031302060c12180102030306010212090d0f0b101707092d0501032f0f0105130314070b0712120b0312030f0f060901030b07170f04020103 71
    0x80c082d00800d4105c1f02e002c000c10340b41d0750700c3d510041c000c0c000219080343d000004100e0f400021408002c400c084201600000c1d0759000b02506203042680c0540e13510b0b042d900248204841d03680c0100d08003410251b8052019519910413000030f03000e12841d14001d28500c201e155603028003060308043c0348201031071a11101c4060b110310078640301445201c0d00e028a075003c100d050107001c410f41c02050340c1c040042c10701050b040d0714a00400203100a030b190501404d90391801002031060641c40c5030145a00340707048034011050310400840c00c4072281d106500640401400550b1070340f044040f644030307514658650088a80b6480c108071180c240c2d0390081101d01c101400850070440d444111030324281d102003000340c00780c1c48107000e4880080e00d19070300c408a65200702c240f990f03440c248110000100c1407507010ba6640f404909624906001030001c0d540341d001181041450b84400340d006054031341041c01d1841c10344d600f02d0101d4081d4104900352038a500381e142031001050140c655940194402d072418006403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 129400296 1250 129399046 129399089
    0xc0b06041d0f0d021903111e0a06050105040c050d020c0c030a0b040302060c13030b06030a050d0f080c1614120403030e030c030607021902030c2701120305030a020307020115060504 79
    0x61076150f0480380d002c1070803038a217400030b406100d080303101021f2941542c04002460072409004100b000c12049580c10000c0c2c0001048140d110366405403108903420032840d200c00600070000c0c01880480d044499000542c0241c00008100002240a0080031254050070510f40101c0052058404030054424030000c00c21b843e1885040e00c40382c650038002c0350b400520350385940020340400b42003240c042c0038000303c1d400070074424042c1c4080b8071050344035004103840c9101c0c001c1c90044000d0034201010000d105c0410802403c041c0701c452203400400290000c484650400d0510070b41e016080c4100c1800240001010b03013001217102c00c59001c4096410520b0f20f10149a111901110741c580160401220300030001c0d030644400000701d0015044802d181c60700310101d40000c2c2b0071111555136240c0d59410b0444040503142c800d015200c2d0781580c44000c480345ea0086d150b40800303020f148a1a401000140c50217100350702c0040850403444011181c140c0ea058090600d501c5401036aa10550349500c2142c00b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 129401546 1250 129400296 129400303
    0x91503070807060804120e090103030810060e03070308031b0712030b041a09150a03110f10080f07031811010809010e0703170f040602060106021506010c0b06041d0f0d02 74
    0x102d43e801d890b120415901c503079694840441312200d00051064880d1190020f0300ca48902c2d501862298450740340174104030303072041116080c44c0d00c142e04100c1720f822030b5881c4c1c0c0c40100700d2a0481e0790060700d0b96180d8803485111014200000ca410341c00030001315041c014072000701d103141c01d0145d194408101039850101803100f664140ca8404405154060b0000f00038200825001e501003a02c0e90b0507003040c00c0802c00107407100101e0b48241e9141d0307101c0386100c169250490310075000081c100d40101d0300030803051000d81101c04c02810540312000c1c81c80061354560181e008020460314505040d0001002c914100900074131030340500340050011400100031060510500c1024485c15005080b0300786550760b204844207008844240a240510000c4511441c441c080c00c003a1010b50041c0c6a15810701c207000b480c3c24140255401c41903550014032017140d80081c1c90540039078014000d09000e6a41102180c09007007105005548800c480700785070311102c40402d10034502c900400c10f40b645444402e604076503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 129402796 1250 129401546 129401549
    0xf0b04020304210e041e05060102030c0a061503020406030b151203040909082a06071e050a0c050d0309020901080105040201020c1201090b010b04080d0f050409020711091503070807 79
    0x22070349018140c0c083c004889400700840340582c0f501d10394203500e502c041000d5a501d082d1a410101c00b00c014052104c440d0b000315540700c102807008508207690304001c41d44c0d038102d80c80090586a074a1945050b4929483c0629001d9a000ba000744202940c0b072811600444089541d0118210001c005400c18170340341c1d00d19042c01c100384000b141014200f004d03c000801c15800c04545004040000c036090910564003150440196500003402c0c01128420364105600108102c003007080c1506511256240355404252101d0280b03006611504980c070305840100e0b0120380540144190300700350608a905810807011140300781e61003410340c1d0742d0b207800c0c17802da803000c0d500240540c100c403c102c0c03290308242c03510b401c4409a0f840042403c80f01a111005880380c20f820000c000d00c0c0c00a014400824100001003820001d0710744580c00d2210584000e125004da030042c6007803d0740001d01c8406100d5200d00780c4d400700b08001c3c0703220314604007410035858080314400c001c2d00078090541d0000354000b0109d0b0610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 129404046 1250 129402796 129402803
    0x60b160b071409041116060b09090a021815040f0204080115120f0305040b0c0703020f0303030601090e072606030106120c05010302070c0902030f0709080a031709030912010f0b04020304 81
    0x9081901c0d01c42040045d001c0c02c4560340c1014002d00140e5904144002c0b20000b02e40034002c00140c0760841014048034840c010080d45141c0d22901409005840b0b80920720360b051500e40b00b225858135032003299040400319041c1150300604107802d000441b00303140e0003401200c0c1818020401c100d50030b1503c184e82281ca110b010703c901034103450400416020001b001c01c0500c40d1921b1488d05407241d05c1802c0d40d0700071031b660090b10b500000b000d008500342889821503143e0124019811458004002001c03555075000f003c56035031020f030110300402d00860000701025800d0030a84103440d12510420b808260880301c10b4800c1d8203100300025242942d203400c2d00c1c026002070503a0b517824201030056000c2c0d404540100c80a0440400028912900b807000c7c60042507000c107911101d08000c0c4009000112541200742583c000903441000641c116441c1581885491541201e5540d010302c058114040c002031160020191680390300003031419440b442040704090002c010759880c4205000c00c074042140c005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 129405296 1250 129404046 129404087
    0xe1605030703060515030d0203040e07080105100e0301180b0f0f042f0d03050306130b0f130609060b0d05070e010804060b0f04060f0e18061306060b160b07 68
    0x1072003c141d698010581c040d15209189081c24421400b003890080c00c0780c01e40c0e0050308041400d04c680050001c16a80194840c5003240ac5541444009a103104130b50040e04184402150f841800392804e4103d9642c49900c070900070203a04c207a00303220070840c00031140c4000b42c101010025101c401d000f1401d074000d13604581207040055103800381c1d801d010001a01070700203c20b604002441741c4c3d6540081d45509100707039901034990810744180300d19007a1070a83d40c100d0300d0410358000c5040e16005408141c071801194101c1d110202c4245210003081160410065a4148070300400e20100d41002050600320206041191f5680c1074800c6400030744815080380015102c80203c1c0c045403003500724aa01042c002e015107404068800003c048070429885840700c11102041007060003441c92426500c4102c4002c004202e2f42e8050440e030b26024024001c6200314807420005081c001a0340c0080064404d0300f8139503035145a00045141c65110020040321a80502400100521312a03440038a400c003c03200403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 129406546 1250 129405296 129405299
    0xb1c0506091e090c0a0b090f041e0213090903020102040302090c0307020a1112011409010c02070b070b040c09111b0c010e0603070314010b090108061009030807140307060e16050307 79
    0x2c05103000c9014180c44414814004d0704041e0703070790755041c180050400084140d940e014050a1200b02c440c4543e42d035200b2845c2141440001100340d00c8000d40d0b03101904010381e2034406002420032181e05800990300f03945003054440806405500070025a07000b2a00703500300707a0360721040162521081355035400613042884d145001070b0716611402000d110090442464800c681c000b01c0c215000060f01c0c008403080d12080c030001c21003e108030701a1800174800b9082c01403c01400386818800c180c001066a2041b00010b014002c480b18500003500030080140300c43c4406026031000c0380c1140e401d104031000e56006d4190010400140b980c4012810784810029510020400201707820040c001010326440e80d4544a440040c981810302a2242580203501c0381407000005005500003810030b0b0250300e641880d149200d400001410071294000ca80d1907607103c9529044000700e0341c2140d00f086902c404541c2c01c1c20060690403900c000484581103d01d01e41b81c150f108040c4451078454150140c010310740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 129407796 1250 129406546 129406591
    0x1032702010c170a080106180602031204083a020313060902031009030c050709050106020a1401060f0e06031507170604061d0106090605071104020706060b1c050609 72
    0xc2d40322410340a00c2c10360000003c6441848625448000d0800c0007171190001881041d400032102c0c16040445c42c03044c08042c0c20007001965900c64955003054030008000000c1c200900d4004888100031490300405540c000d0503060440c241105102e1242d4440c83d80103284110114400d4034418240003540c0c440314071243c0c58074001803001010036a051300810040c807803402c0c1980904000544039507075008580d1458145030341011415040342d401c640c00c1c4401003014a03400501440c009800c03c1340c04082500191850740149000c0c2d0050740e440d044540009240340340404040c0c0701b40b405030190380804044041503544003d0840749240440c07500300c00445600d5845e40d8855100c140600002851a1100d000b000a8400044d00c402421580d02c018081d5550104828000b80881d051080c24800c1c260340361460364407c0038996009a6010035600241301c101e400c08030040c000403414940d58100a40202185010061146516818540401d0041c00d151170351900c00e0150743c10501200003c0b11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 129409046 1250 129407796 129407807
    0xe060d0b010c0507140414040b04150e060c0405011b0203071403070506030903070203070801090f02131b0906020d0801031a07050c01020a050405120a1203020a0504080f06060103270201 81
    0x6803610304005801c1c206400064042021502070105d4040c3e0074100d18400313041000f41c13120107810f4403100f2800d40511000480054846401561107648103551509024801005010b80d4090807860722460043c000085e124000402c15a9001c1e42c40c802c81700e88440c0320848029202c0d800a4041d0300028040000060040c0600740c400b03001402d0310b9403d0b03a2880040c10940040d10030b080180c2000031110214902040001d00625800b4002c0c4802c00f101d44074090b0669401e040a07004004910450035000d0003a4460b1952681c100200c1e03461000342c0c0e000409280d0b0600644015201e44406140c2d03035030003400790078100c9a1080b00482005220703400b0b00d80111002c0c103400d05000c018001010a84820700140c83c40944940e200c5858601d42000c10a50a40000743c2603d980c01088410380854549a00e41d12086003500300540c3d00c0381140c3c81150319100b02d62205100340900b01003060f41000c00b040c41d034042c1400b642c00b80b010781c3c00510b501840f5421821810156501c4901240055001c6d9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 129410296 1250 129409046 129409061
    0x10020d030e03041805070806030f060402040c03180c03021219020d0204060803040914130b07080402010e0307030b090607030b0d0f0203010b0406080a0b07020c01050405040b0a1203110606010e060d 86
    0x1026a81010f07580c843e50014500c4003103820300f00a81755810002c8065112846a034060800c400904a0982e03400407107460f18030140c0040e0040c0c1c0c85034980c20070700d80260811a50044010402401d41040b403d01c405990f04c2c0d404101d20800f24007a815070b1008002030315060900ca507102c0c0c00d81d0000700b40e080201e40d9101d0b1904030b0700181c5a40e00041c8200c0d0900242008001c11400030607105030407500941401002070001c03442032694071880001c2548000e2056009000e070401c10001d8441d0700040c1d83e030b240b5001c901640761040400110804c503903d1314481c0034000a00490740380e600c0f5101d0650a94801191580d08150300c3c0d0701d1280440d0070384032801e48540c0042c000050b0400700030040313030595403190002d80743d540c4244c460400704a4070381d091a0744240f8030310103004800c2107800002c00901c618490320f44140c1c0c4402c80b4030165518060701c0030046c0f0001101c04900340d07a900c0c01801884a0803010240382c080d100004041d03501807200301c0b00012000f81100e1402030f030b91480400a0031503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 129411546 1250 129410296 129410321
    0xd140615010e01081905010e01151b031101110307020307260306150f130302100c11060702040209040e1e0303100902390106090b0307031101020a080a1d10020d03 71
    0x18450b1700c14503400c5a21800c0e003c6d11a241803a4102d6040840350544800c1580210301001809005488207040050b01c00b0410765044c50800789490030a1a003601402050065840300d4000006204040d0340001c0100046445802ea50440d401c20100e83c01e2411615100301c145a0f00400000f48507140026400f20a0780d40442c129041a601c1201c81d60350b0740045200200d084500701741401945021401100e00e460686028010800a50f646007060307201c0300207881c06000045041c031704540c7c5030340640c0d0450300c02034010801c0482c0c40c1105695042c2140600c90100702c944c100480390320f404404c49200d184610003240ca800e1030715507008000d60011445601c81c2d41500034071040174a4040300310001200d624025441655912006403c455059110f02c07071441c40d021f00b41c0d90544000c110581200c2e04840503204400320440140e0030050f1075180144a04000100f403101035070040c240e00c00c0722521110b1980402148418800450601030340c19003d0b038880c07448400b809100303801100410302e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 129412796 1250 129411546 129411571
    0x1201051c0f0c061d030c1504050402120a051003080a12110309010c020715020703020616020a03061b0e01050d0b12010204062001110a03020d0204050d140615010e0108 73
    0x1031901c54403401515030000325040310121004000a035070100e006005030707030040c1c0c130640740011203c006640c90039082c00c0d1500955440c0322001c58a040542a10b00501c4040c1080d544c030000702c0c54141c090079085031045445450000800c900c1c0c542440754800340d03039110451501d06140082c00fa9100e000080c540c1900c41e440361412908449200301a5008400d0300700042440d1030b20b000b000c0e040800340d4020b130310414144030003050580da000840c001125015251180e5804490004da41020000034010f900b264685d50000200801d40d40b00b01d010034410030400500520303400341111119a19415140069001e0000200801c3c065010500c04880107010010a0300304140d140e0998001e42c2c040d40c0440c03481a1255100820020361080e85032119000b08035901280d03101589070b000c2c03050208100340e07000c511a500d90000ba8119006404c0c020a02c001c401c01c24984681005103da942e0f0a5502921001c9070405022224030115000e050711034204070342d40c940c01102c42c0000103100050020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 129414046 1250 129412796 129412849
    0x50a02040f03060207020111010513061109030609030a021915020901022d0c03060606071209120c18050c03010b16060c030b090705041d0405100c02060703060b120105 73
    0x603807890030240154424800561100101d0001401d0b00d00d00d030002c11701c030780d04000c10440000c2414074069549640706000050400e900c0e20503616a0240b00c2590382c06100c1d003c240504020004003074928480594200c8441c0d035641030502c00c08550596004000c41b12410382020118840d03005050303004410f10445803141903100d84102e8546045210307418058a0200e2034038800401d010340e40d010300c0e054004144608290020840c240f03d4118050f02695a0800c0b0080451150248100030614007083e0040c056490030541c07a241c41a108840d103030b000c10021040410414002c0602c2002c034500000d04580c42e01001c04459030055944174022600c1c4080310b00026120f101e81100030005540000315200340c0e00078400c075014080c0a210620900340010003840b03d8408042c120b40805031148a0b040c0c88070301d461860064a800407900243c2046080e499940e4001000b911601d45d07581e0a0010980e5404007041c10300c125140003c00b500e2010050200d8185514071508004104008450b0103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 129415296 1250 129414046 129414059
    0x50405060a11010f0908041d090d230c1506040e0a061a0a09050702070602030705060a0b06070803040318050a1802030c0c06190b1c0f1b1205100b090a050a0204 70
    0x154175101342201c041202180c1440500401440480030700c1042011003001e09121032425030740d80034030020b0420414045c40c005600685007000140190000428540ba01c00d001401ca440d9120700c0010810920802c0004c3c06521381402080c030a83c5046003c0c04c016503168aa0101400d006840c3c42c0c3c5010280400105c1038450f2001c500041031000c1001070641040c040003420078500303900c01d02c115482408047d000c1400444d02507003200341390900254021241d00860010f000d10300c0e025184c2040801040f0905402001100b1248000d41300d45036039079100d408000c04c0a807a40580400c0c400007140a1010b0381c02c0c1c0c0d00958018001a648604000702040d80d04c1c03401a003100c11a0441100035004154454139000354480c0c0c9030101d904070810f400005105000288a4002508600c900c8040c10240003040031074540005074032100403862915090116000030340310904803650f10807082c4040360350301c291003510030f1a200108011f0982e01e030b244560002c0c003409010001e105030300700000600d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 129416546 1250 129415296 129415301
    0xd171308070503010b0f090a0506032b09080d0207180204080307050312060f060702061c06080114090a110d03020f030304032006060f10030b0a030c0f06050405060a11010f 75
    0x14503492008100e914144010325007940c4001e1700c018000d80d9101e031290300325030320301c007003103600055031680000d5664078200001c1ca860402e076002d0303100b90036426081d501a8924820301200003003540b41c6002d1103903a014416a6064a207424030010b8004000074446110000801c10b409450004c0143c00d168403125070606582c002c1c1d44c21070b4154000244a01d0703121005c00900c0e403115044072481e41203524900443c40d039100303940000384607240004800d41038039081c40400e4101c400c12101000802c1d26521494000c003004034015040400650014001c0038000642170141548006444030407100d08081c420128180e020803015805110b404c0309074060108061441107000340d40c0d00a03c1c140718a184640d030a40c0901842664010300b04010035a01e42120040070484240d40c442c4a1207c000300440c02060006039143d403251b0b091800200703000001094600341c480700c49860041c25610388050326a441507106094002a0512441804c0703070185201120000c0007000100303807020701d070115408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 129417796 1250 129416546 129416549
    0x381038030a050906070201090203030d0c02101b1d0d110102030c030304110a0b0c060417070506090c090f0709060c030309060212010315020a080417040302100f0305060109050d1713 79
    0x7440b9507800030048a40010002150003840c0c41c0000c10803c2c103075030040790f12071007485032400104c0d4480d50b45040d02407080001c404001c0e10051b0411556110300a00b0030103030f5203960325000042e206101c490140d0340341e0a0800361240020412407071140c0c195550000c855040003d1130542c0014001d400c078020062008501c034521803a0000360300340c030310001c10452110390b402240d0322036003c2c401042d00c40c10004a081c2c002d9002080807421540d00005044030b881480d100815030b004e000d0a000c00b0302e40000d5074015514084035000c0351541c469815441e868022100d010009403186000c100c40307030244c051005014042c1c0f0780840c1c01011601c802c3c090780d204010104100c003030280104148000140030740848410004107515140ba014001010030704050b0020306600b0f503500c4800e001481203c21140150f901815070800d0000703400c0007800c4c48000e0135041c3d0200341810006142984104403c5064070030050403182d20180c01c1e03e9002c002c42c440c1501004c1031900300720001002046800950 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 129419046 1250 129417796 129417811
    0x1204080301050102010c050304080d051015020c03010609050910020a0212040e1504020a051e0409050f010311030304230a0503010515150f031338103803 67
    0x36038079450710b000282101c01c081c0381c99040240034020702000500d20000c0340d800020600d00840c0c26101d0506c21050700c003060340002c4c1044503032041000081c1d008540200d450310220020010156945905816100111004401078025031f60411811809501400e100041c0b441143c03c1ca0035074080e02c0e0301c158442c1d0030220b0f000354048108203a50603c565001550b000540c0c055050200020014100c0e0240c1c00300300040c0c248142000240070803580c1900c0003092004c0091080d41002c03010210300c0a8203003c20b1f56114880707100000b06082c0041210100d40c548000c04046078000180301e10744010a030003ca910001d0304800091640e4240100c80c00746089902d158840c100c10010008500702e0001c1e59802c0c8002405144420030004081d00d40c0f107503030305001420f01c04e1a440d0403038044a41c0785d02060300301003070b0041443c01c038081845640035802d61280d1400c1c80d1501106c0200703094285c0300702a41c90500614004640014500000d40c101c242b500c054210b698258420801c1d030030032503009 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 129420296 1250 129419046 129419063
    0xf0204030510090308071d0904030e03060a1a0f0111010606091814070c141005102301030209040204080307050c031501150c11060c0d14090105040e0402061204 70
    0x1482409000e10020a0780b07262071000f0424004555806808100010205810720080c24000500109011107103800d042c00240410503510742032801600d02c106032010180a44961000604c0500040c401c2200f101c407410202421080a602040000160059020304000c0b40920840c6000760901503140a0081381d250324440c90305040641188600d000c160300f0b100350911380b1a40341c02c0c403030000880d048812450107444000d500c0c00c1441d02c07584001d02c10711b070710f100b420b5440760350041c107501c070034000c203d095004407019603a20700348020100062205908441080c0c0e6254096000354001d2002d1907000c1d2015040603a5206150700f0354000007400d4985400101e0740070301d0740c0741c2031040c040804a805012040d5504010000d65000f220350b5007a0103105460205805010f100010f01d0403030000100141e0780c0e480482d14003070311150711700c111501064001042030050304095042da104810103075580d600b03051a01500f6059984040d20036a0440c000700280e034161411007011900c66809050107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 129421546 1250 129420296 129420299
    0x10609082a0f220507180909020609060a090501021516080901150303230304031205060102100606020c040510080d0507260304051005010308030c07030908030a090e01090614060705030d0f0204 84
    0x71081a40c034000c02c01810486c1550a4200f54103c0001d01d03415030314036641c00103a056040c40400c0e164881c140d43d0941c0b005001c5144d5000c0c1d5485060541554800e90941e103406110501d0b21090010541c1c0c40440072109240c0808050300c211011907004c2402c00000c540e4195031406100240301c10342040c1d0028041c0440c0140e800d512022111803250324011040c034515058400520307040c0b00c810520141500c5502140c590783c82001419806a11600200038140e03844c1000703540c0e2015000305a004034202000944003c0ea4800382c54125542c80001d0308012141002c115440d50124504980111440d445d0b00c021450300e2a202c42162101c2c4502650b9081c1030610614100780030a07110440e5041c80d00510000790400c05881e0000ca02921881d110300701c3d86403d5903500e620750040c1009110105d8032800d81c603808000d02e000c032a0003581c02d80c541d980359884401035605c00d0060b400d02144940300c3c1c18007402c02c0e134010a4140d00800c05e490624820302d45c8030042d2038400700c100a010340c010a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 129422796 1250 129421546 129421609
    0x9010305010f03020307030b0a0204050319230d050f070602030106050408100b030c040b060903010e01021306020a0b13080409050709090c0206130b06130504050105010609082a0f 78
    0x80381d01404101140082c014503560010342ea661040c00010b00c284601000b003550000c0c9a010303100940340c01420b0b104d0b180592232445005030822102a14a00f411610305405074010790175440d0420301070f4020384801d2400301d00540d0140d04c02d21001c08040c40410080e4042000fa00c042c5018114581c0c583e640c1d50b180110f40351501c406030182802483c07604907000010342c0c00203009141c0000560303011690150581c0061401c1c02400c02840d09542003601c18500700c078043d4010020314080e401c19442d0305881b985d04981d200183e040c003d102c0f0414001052008240074480004c05100da103540e03190030b841d242c014007552429142600460740001c0203000c8585503000f090480780c603510091156281481100c020142c400c800070b090a19010081455516034000306500400400c00030f000a00785464180d0081c10300b4466180042c190104c080b990386000f003000c000081c01d03500c0c0008107086910241d103d0280d407a000325448071103001c1500d02c68495180c402c0900e0050310014128910009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 129424046 1250 129422796 129422801
    0x10302090c0a17060d0605040605040213090305070b0901020912060f0114010507020f030f070b03041217040b09150702150606091008090a0602070b090f06070504150e100203090103 79
    0xc1c68403a07020800d10003111040e9100040c0a01124480c50010207600d4040210790210404100034203a036050a013000140242c6030006070185100344c0da101510b83e0701e40065811580c1c2984024000b6500f00302d450301180961903d82d40000b000e000040c5014004400142a8502c0368010700301d6401801c100020308686c26040f60040a000c601c4c01c3c1108030302000200b0301e1260840c001d100d2403041d0030901c05601d0400068604000c8c0404447c001d5456078841c843d190000c079403ca07030100c840d41d1a04116071141c0080e0081c55128002104c8a40b141e681e80071800d01c0c000c2016030a4401c03212950343d5002c503d41c1e01405400380740c01800c1384010000148000f00d200504050082c941081458065203910311048001d01852070a140300e6160345000d103041c03403066040500254004580d81c0c05002d06818100e00440302c010485400c03a10010405803660000c94040d00803e0060000b0003c0001c6005a0018046207207004551903e18900050628004480c840d0041c0c4c000300f0035180658152 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 129425296 1250 129424046 129424051
    0x7050a030215060913060f05190f0b1008041b09090210020c030706050a0e15120109090f1709041406010e0108040f060216080706050406180f02060c030c03070b01030209 74
    0x20442d00032854031a01140740c00300007a110a24006110300090240249a88201c0038800c40d808280f10343c0c141400210241c18604078000402c03481c00c420b680507100144903425140300c0107080114524101d040c25144290000c00a032608010040c554406100d1b01700243e024011805000a203c201c60060102d003140d005540400d6502c9190144540e40d030000d4418115890362910035a10f02c3c000f0300c1181c140e542604a1604210070600d2118940955000f4000c032502141614400c1ea03079406160342620140034000d000d030104010a10089003a40118030001c0071800c64442c039140644010034129564080c01c0c01110710401700340302e41c82da03001c01c400301c0c00e41007442c0c51400da0130aa1980607440c1c000c8440200f545a000070810101024034214100450b00301800b01e4031f0710400c1c05d00341d0140100301c5080314001d01e00700e000d00c000c948010300c07040c00da600004010302c2100c00b982802182c0e4404002c40310548014006000c140100f00000c00555104a1000d45507524600c103020450f04003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 129426546 1250 129425296 129425323
    0x5010e090a05060114010c052d03040b0f0a031b110705010f02120307110d020708060f04030f1101110f12010605070503160804170d1404060903030e041107050a0302 72
    0x245440002c01c10016009054074040350803e0700401c0c01800580f05a498014010098000c51445641008500c14842480b0829050280a410602c3c0242c0d8480c07080d409201108082448804101e14142000d040d200d821070900003a0140c80e0008c8035000000d4180b000c0c00515144001401c0c08800c0c803a5000070310081c02d1040084106800194070b8058406101088440c04800074036582e1142c0350903d00108041700382c88070701d02e49220003511043d141c080c0040c2403240c103001c5a41c08003216109486503815540b80b141c201d00341d24048503914218030402c00c1a40d25040844c0325010050010070000e000c0e88007165075050b00b0391203041c030000d0582c4001c081c41000d0202c04045140842183c021490202c1c8080b0700c1e216070318000d0300038081d64100c0d1565805600c0c40c488100030004031102000c200d070311403010360940f80e003006040f80f0035802040d0000724000c008200003402402c0c4040d03c0701c4010f0000c1551928481d8010301034102e00b0045d100f0b68000408801030580505c400315502c1d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 129427796 1250 129426546 129426553
    0xf04110d0506030c0a0b0c0106080a0c030f1505090705180705040506070501180308091b1e0a08030f030f070801051f0507020307140307050406030b010e04080409020a0305010e09 78
    0x20580a61840c0103000241218948501c0019503030b58083c0096850181c006201044841d1100301030707400c5401c070043c441919031800c0b4003c96102e000240c541e5100c0e9004201b503072080e0555480009001d044c1ca000c80d24880c0c28510315460500a00404d0301c1003c80e00010008189005d040008440000903003018240181061016840e84070003118191201901d84d80c1e0b0361282458818010701486a42000e40d04c80107a0103c1015030050a05007c0c0003034a0450f0300c03030401c140302503e21750348041e04a0351044600d007040044490015049181d41001441900070039aa08144ac0c15980000700025901c40700008000c07180280c1c0010301d802618606e0400503943c10603010400703e00305228481b000040080080c0c3c402440740b82200c0c40a980681034074011a582e0200020404c145c2d81c0061290240c01000715543c10b02d031198500700c81d00002c0d09001c0764a010301e5000c0701c80c0054002d0722101c2c000c120218513010f850008140b106000d41c2d00081641c9000783c1d17482220000740015400e0382 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 129429046 1250 129427796 129427811
    0x6110303070e030a0609111201020c0607120e031306180b0f0904061809050f0a05031b0c090c090405060406080c130b0a0308030609160f1202070b0a05060f04 69
    0x1400410390780d0112903400c05140b005440000a40f0300110100e0040201d4101300c5004200952810031400a11041c0d6030030200e8501e5079225400d0f40a19800d08941e0b612030300004081354420254505100c3d0003490014950503c1840517046620400001c420b00071210740402c40c8617446842c603038164800380c458404190900036003513410710801101074000c22000ca4034018a41c1c03103500c00d000911030a24410f0010642038030307210141c0f203c140140c41074054003680001428010400501140d803003c0034500c3e01000c08148405120301083c0c03086603100b003161034032290310740352046409400040400f58a50b000789041000380c5500a0402e4040c9050100070000d01c180084c840e051340700101c4401c5070f8843c40b00c59000080c0204110f850340684003070b5001044c840d81c2c800450003201e040c1c840740c05a54031408c1010b088508110001f0000d155030b0f1000d50000e12450301406100036640d000b40c6441015200c289201400359100750125580300f06000d5649040c1081003078000c8265000d20810 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 129430296 1250 129429046 129429077
    0xd031e0b010909090c0e091c0e0d020910090e0604050d0e060f0307031136030705010804060216111c1101050f040e04050309091302090109020d02070606080f010606 72
    0xc0042c3c1c41003003060b64541d0300c2030342008000c03c113034000f0b819414441c00542c90300d02821517549450b078200440d080f01450360313861030342c0c0300c1d0010040c0c0500c06403039625000c0e030a60034032901a41c02070001031183c00c07460f000300b41091035000f4141e01401c40c500500311400c007400e0a07428590b85200060a01c201300400c1a5562182c1066407081201180a181c5a40d100d14041d8080c0852444000c2c03d50000100b43d0000c020f02c24203a00700b804a00c00007643d181c4401485580036215040003603043c5d0000c81b08004030f41c0b191130031a0344035209900140c103003074204030000c0c1882c0380c0716000c41d0340080c41c820700c40f61424652018040322141d180c2000e00070707c4944070070001541b1550304a040000018040c0810320801d0304032801800d14080001a80c41d160820342e48a4201c03130030710380c450090440032411a14020f4206107507160005c113a02d4059207481c5124000350320401960f82059000d008500103d08180b0489005004800150000c2002c039107103d42140c9540e04854144201d0012240c0310703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 129431546 1250 129430296 129430307
    0x3030210020c0109050604060f0f0204050a05061e0708030406271e2906010903030504090209040902040e010b10020a0b1816062105010b07110609030d031e0b01 70
    0x2841003005035240400b000d9207014201100b130240044c03107004184004c002195019140e601c500c0c420410084448107460405c0c0e00c1180b06443d440040610103002d2480c0600051141c900c42048994000d0601c0e034110100e50001e420a8402c40c43c0401000705025240c00359201107103450b18840202902e001c80418446105040503000609182c080718080c8400701c00790181a40288080c0170407001c081100449034107e0100ba88000c0d401404030b100c55000c0c00340a415240d0646aa90405040c915184001c0d008266015445038030b9106c54800f40c1c43e113102e0110100b1169001040c46031152061000424005071004111b42c070082014012510310001c04d80c1240c400c281d543c900d088190826850058500e88462514103c60000035140b80c1200c8540180303110315000307804a462074042c0b1405c1318401d10542d884210104520b5000401c20b050707195504030014540c2d42010307040d071b0201e85003200e42c1110002080d42c03004910080d00160b091004d80600f0414180300b841600c6000912 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 129432796 1250 129431546 129431563
    0x6030807061508030d050406060605032403030f0c0a020f0a0b07020d05030d0c021f0c0f050d0e03030a090212121c020403060507171b040b090102030405031207050d09030302 76
    0x60355581c540903a2240d0300e00000d500a000c040110398680758905c00b1100200010b840444216141400014034940100150b922914100c41544500002442d10074888840d1013420365040c08104500b68810030700d8000742902c02e04078030040074109581d1040c04403240707403100404d1003401300c8001000406071240848113010780c1038400710421102843c01520b507000c0c90218282c40741c1800080450117600141131101140d0310005049403400760400a001c8426113400000003071003183c210010280114010851001699800240a101c080e0502d00f103800c2512402c00c40b80d111020f42095142418020344104c0980004e45201c0d0315001c070741d0000b481140c030303400e8403109050751807001d50000d03a0544005540140b014401031600c180c000740240c200e40160301c1e074520380e8400f254400034551256510098803d01880c039050603c4c1c48101e09070826000d10381107100030440800e0940f82800130f12a800141c1c1c0350b0079128501031515500300f5a8562000080003012180ac001283e030006d034602 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 129434046 1250 129432796 129432803
    0x114010b03071b11040c120906021201060e0a030b090c0d05010204090c0201020c0303070c0312050106020a1208060114030a09060e01050402030c0303120105060310090c0c0b06030d080402100e0d0f1506030807 91
    0x200c080c0da802c6c007507030301e4501c01d02c070b507480a8031f4041001c050003c150001c107207000250107804400da0302c0d504140c560411400b8070b160803400e0014184001854507140715040321495046400c49107110b000601030010072070040700c2c0ba9401081c2008080f40303601a03034905260343e00095007407480c81404036987e808000d2403181040103030315581003454011107200d41003081440d0140301030368490740003070350702e0010400841d00990302a940b00001481464064010341d8141d403a0840d42032100d225202c0d507003003d032041c5040780d55031040d40000761031442000798004c1690004166890b01d4010507086c041400700060190b0010810541d0a108456030b2790705459088a6554890315805224041c045054101c61035131440c00014200c100d820030318134000c1d81d02c29009a0bc2c076035202c505040e10f4058142d0050003207108000420010310700321b501d180d045142c42c50044e0000c0b400c5400603841c1846600142d0302c01c2c22000010041c800044a05800b0340d00980c0148110752640c0e03141403540c4a02032026 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 129435296 1250 129434046 129434051
    0x1020c010905151e0f0406090b070f020d03050c0a0b06150301030b0f040809040603030210060b130e060f09041202010c030203070c03030e0a0803070e0915030604140114010b03071b1104 81
    0xca4404d54650740e008510314040c00e45c0750744071004040120760050080b00003042d11980c00040500d221811182019070000c001c1502804a40c00e00c1602026044120203009080c084c80020103810080c1403546805504e100c0a103042000c00d1000c0602c003212042c0c0c0c40c0340c00308010b10200e0112401c658000b40c5408d546aa580d41c0c0c0d01b440e040038090700381e025520504158001082c1540010740300790b0020505000c0001958401802100d446160b80c41400d03002030110402c9613070003860505a10243c040c003035130391b408507081c005004000116400c4910007108541e400d000ba909220300300e2454010706045156007010a4060050401310030001c2c06c240e129403030540010010302c03200c481e103a0302100058036030510090160806d800b041e038031030251f038200c0001070401a02e103100885034100130f070242c0100d8603a47c54800d40c850558bc0860880c0d92903d011944003018245050300800107600c0e46a10307402d007201c00504d0465003032030086103d40d01c00100004145001201040c44100301d800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 129436546 1250 129435296 129435307
    0x9080f03070b041410020a030e010603110402070c030803070201021b0106120209040807061d010c020115140604080624010809120307092103030c051204080912030310030201020c01090515 82
    0x711003401d403a44c0406401303020b8070b1202280100150082e090000542c1c500780035044090954a00322091072002034140b000e102400c003500c3c03c255000b0b2130a940505031b07508a542d00c945408040707500c107450000041c0c0d40000e01682051000e5520210400c2d001d0003840001c2c41d122031076085008181e000391146143d44085000c00407100d01b1616210350144c414080c08078081800045000310003818405175091902c03004100e0b20622461400c0404c079000003000c0e41c00e0860b06003507000707620b800c04c0d04040100408200000100f100e54841c01703060804081c000c4940b619041c05004410146051100c0c400c2408070a003804503c07080c2114801280315200d690321901201c5415060380302031142281f10b0805034603682a80411966039009803014040c0c1980e03254202d80c544a40500c100c5000249004100001d1840001700100c070b100820703020340e804440c52440e041d98410365205418034001d1004000319601402100d00ca0701007404e204020610701008541c24510299413480c503001c0c000760 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 129437796 1250 129436546 129436553
    0x30201030c051b0c120a03120f291509010c021002031b0705032b050d0902040507031d0c0609040b15070b150d02060a030e0a02060313020109080f03070b04 68
    0xc0c0c60122503564014140d100c0c0c0e1104003621000b408841c3e038050389001c0b0250200d0000041c06e80b400aa06030b840d6441c080c0b090020100401c05181104405900c2e000800844501083d0750165030341d108030460588000141081030700e0800c4400e20800b10024404007031642e820a0001044640584140c0d905244a4600724114401c0b441c04079011004103000503190140010298240ca006604031070102401d80e0800070030758268565143c00d5505601035400140c401c40c054032002c20410004100308074a075000500769a421619500020380d60795010040c41101b0f200320100b105000090301040e21464007082c458803c8005c42c0b40503948511004696499030224007003101c1184108a450301014580692042c2068440041c20114005403107260f241c00311610010340e40c02840300c0d02d031803e050720540c0a40f031154030500240c0104491100543c5035034008600c102034452580c0c07068841880058a904e4180e00f00d0300c00d0354041078000d80281000004c07140c1480d00402e07800f003c0d031742c1e41c138 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 129439046 1250 129437796 129437807
    0x11150a0f020105010617151503100e102601021c02090f0a030507051c02030604060e0601150504030605091905010606030f091e020a1e1406030402030703260708090a1a0301030201030c 80
    0x1085230302c91000204003e20b080d0340c0c1da040e4081e42e0604503101c8051300c4002400000c180e2a000f00e1101c2030880f18030103083c4d22502c1d9501c9049001c2070000d0304044100e908001e540b814510f00500f010340014101c80a4507007101003008080048900914560450320b80541d40d000300e000342400364403285029800000c0e0412203045003580141103030074a10301031412102402030740d040000107100f40000840c544240c0100c030b1303940e10400d40e02c45051034515202d4070060301e4090b0020074075000d6030303c81c280364001c8100d0901030640100300228419140100044c1107a504c510000207080c0b8048003000043c00e030341c03000710111a607450411102034240c00020900a0250301c40340d00461400c0c1481d002464040852013242c80c1c541d215001000c8000034080b40e8070044400a506400880c41400000c0210854200569080f5446224490450303083d4259501411040c0c50150020070786070303014585840107002501c441c842d070318a0516030316451907141c081030000a05054940003e07180007807040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 129440296 1250 129439046 129439069
    0x1115150d050d09170a0b060109050306090723130e01020c070e041502040501080610020c060a031407021207080a02010902130b031b060711150a0f02010501061715 71
    0x106222600c05091506694501e004480310300400d4404000050601c0340c07803081540d0b48401380c003038907013403c99a845100c03404005002506201501c0800b003825182000784611071216600102845030920402c000902a44030001002e1460b44080701025200c014030001a4040c00f84007003a004014451580a8010505007601034480d0140c0041d00c1c10740945998000d90099840d8104203001543c4641a40700303c0c015035021561500104009042185000e4407481d55032064840101c0b4032000074060381c1c0442d0200c000203840c0c00d80d070064030000307114854100115000404058042c0c6243c9815030041101c0900110008206070711101d000f900a980140e074002c1c0f01c00c0c41102451607160041c10020b0807540a4499a01c03075100410800a0f0403900040090111b41442d046940c0c1c8694045600c0c1050b0b00080e059220210502c0400013410607a0025180e0000c1d9542c105002400c449050b801300b4104921402e45c20200e1005a1482d03410200041c0d40001303000c522008a060014030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 129441546 1250 129440296 129440299
    0x307140903190204061518060f09060e0d050f0c09060f011b110603040303090b100e16020a060c0e2b080c0f070b0a0207050901050a050f0112022206111515 68
    0x1201b03107510810f50700c030f10136898182d006802800101d0300d80034122083c2c2c0c07403015080d001c10804e0505201840c0181c0d95020780000c01420160010740c1680d91130308103020060b50b40401e0f4403464030700f002482c1164034180d01147c259240d41506101078002002d0902220010f000f9202c410800814030918011002000c0c1c0060020340e520300381458024020301c620b4005540000740c1d18045510405d83e001c89400f05c91443e0200382d1607450319410751140301d003404000b005600ca0019000c0c00580705001d900562441030710350540809250080c8100790220b0044030440d051714441080c044014500c1e4454a907802c04d0030291201c4a00c101586080100101c09002d44104000001d82c21420340041c0000c2c145a400d40303100640e180180240c80c40f00b070040395441894000203010b5810b2070007000620a50502d045201440c12140c0802240d11290414030903606c076600700011849a4070036103000700b0312442e0046440c0300c60781c43c003134031104001808450a60101c0c045002c0c0382c884080300101040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 129442796 1250 129441546 129441569
    0x1009020d0507080c040608010c0801030305180d0b0405070b0a0507080714030d050103050c03030c0a020402181504082a0d030e030114060a080706080a090c0f0902030714090319020406 80
    0x100da07070181d9615040c4141301ea01c61400d20501084054041c0500d0a008240b41c070b0303032000e80e401c43c2e070150707450781013249084900d01c41c0611000e0715656402420440c04d010302c0081005007021305240f401c1081d16088201020000c000c582c01c4c06030302804503050300c0e42017261031303440b642c641c07401d6040c2c4c200000c4c200c10188000b14062226840b1644480d0480c0d1113030003103a81090354003040c5074583c0100c41300003a05410040039174000d070400e034005211024040425080749015000001e840c196922010180a07801140600c030414080161007403103401103c2c0c3d449d980d02407070006118402c0d0f040c1098080d0300f0345000704080501070800544590704c01802400444444000d61081901c101c1768030344a540b128000140c662004104042a00d44542e0f034803070740e6a16129500d0141a6100e41100c0d2240040c9000031888a90b00c1c26401400540d04c01680c2c07800d01340c1c1d00620b94032103c94908240d02040041d00c1955400007540b032500c00d031100440301c40c110341d030000500404056010140700074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 129444046 1250 129442796 129442799
    0x30705150a0615021b030d0f030e030f0c0d030c020303150f1305090d1805030604080c101107030e0a051f0c02030d09051302210c0706060312030b121009020d0507 71
    0x10740100b2911030307013071417504ea400950508004040d40c0c0c0c003510f0000c4004c5110710f01a000ca00303100c1e0300162514440201124a82003070321000031100d03400100c0c190341942148801d044044d626010fa08884120340c40254190308107825900c1d9800190318085210781c0e0000714981e00e42c1c550240c0b82c4d10703842a41c281000136151034401c540c0c0701c007a094183c0c000035030a08518080d49480e00c40e024103a070b40180041400e43c0c1c13240c1d0f5129050780410900c5c00188149132035151012524060080019201c12142d07480703c0d1f00340345c0680003842d40661680b050f04008400d00050303e83d4480c0710540a004a40304142c0b424080e81030368100c88205c03000c1d4150080c1351240c440700741c0100454046840986e0480c3d00480515101d00c12409012240d018100211190880340c160309081650001c0d10030b01c40c2498090300740c3d02e0108a1300c05520071140400382e450003150081d05886445c680789410f440c44141007003000c48454480c00380207402c1407069603481c03c12007036417500c0d614541900d500504070380b03455 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 129445296 1250 129444046 129444089
    0x50f07030303021e030f04020105031b1303060b041a0103050601120e010b0f0108100608041a070905090612070b030705040f0b03220b06010f140f090f03030705150a06 73
    0x944c403044c603180744002004282546805640c00702c03440307400c80200381c01c500d4686c2d81c01100c82d5030000c0c09091301a80c80920f100a80d18211005141711a1858420f103507072031852030420281c4910b850000e00c40d500e0407400000c51003d070080d0340202d03202407800007540d035540d6005a44042c001402c0340244c528008119041440c150710070380b580c4600300c400101c12a01c0c203004413000c08003250700959210040c03108000071405005526001071003152034820310761503070b11030005084048501400241003030340104001c2c1030040c03c5940008059500700c2a100d1440620341d0b68090714801c074000220000001144540319100f550081c0c070304d03115080041039640b0740000c4079401c19146624004200080c1b01100c1c684481d0710b9010980c0000642c3c201d82e641401942d102955841d28418041c88001c107a07409100d01006004030300c42c030740f0b00c16165220081030080200d5461407480c003e520400402e0003142000a15015012020380064000e585421030440035002651102c0c0e0501c0c52107901030a007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 129446546 1250 129445296 129445301
    0x4141006031b05030105010b0f0304030504031203050403031406010f12020d0908070b01240305070e030708070305060108060f011a0c0118060b0a230f1002060603061b09010c050f07030303 82
    0x26041c0001440c002c540f90001c01d400c1360001c0c07103400340b480002c00c401100d48880340c0c06554040e00a080c0385003003036230300d0f01d81e1000c3c0c1200041ca00300080d5030794100b00c1050341501c0b50a0a0301c03c2c807402c54855240c108006011054461019014404c0002c0d090000d640550116030012a40369400d00c10200c2521303050b030302c6402076442200c10110110000c038007007140340d07240f410b01c07291010401042012110260024078000d40358004000c00303482115120744040080c44014409000105003140c0b85042180c10120181c10003405a00108144002114104110790564200400b00200e80181d6a0920103e2103094003101881d420070007081540e01003d01d04403013042c01039070f00340080079849003048813010b02e40c00f07500e51010714000c5600580080400c40c80f0f002e0300143c6030126010040380003035119501e03e080e240040c1e0001c001c01c0b01c0380c1814080c0070741095101010060240c1540e400c220315000340c44219040202c00201c036010b000b82000b46c100c2d440140c1d13041d100d00c1d03078036803c00402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 129447796 1250 129446546 129446573
    0x28031509031106040305120606070f210c0b0105091003050d0203030106030c05090904031d12010209010315030b061014191b030c020d05030c030a030f1a090414100603 73
    0x11900e0914224842e020100e0598892a410b07901d4074981102c00700d40c0500040007a20039078101101380181030000b004031004011140c0201081d4038034203101c150841c106045001142c041100c1100300c2000114880c001070b05560381210a0b10f140d584440641c1107800b403541c0042d00314420f034a911502c1580110086060f141d866a05014071102c0550540e40c0d441107a0400360481d0700c5400040210340308401c040d00c01d800207070030800686400000104200d02ca40817000669500050310201c07903070148525146191080041c0715a03502e591600c2584000017040c00340a41c0b1000209002c241c881c4030044000140121144d0711901d60700782803200214004003004c0401d50300c07800c0604a2004202540c1800e500d81d03140340030900d840d401d000c450212801c04584078482071150320f9010f2401e10103408004159500000c0400303080410b134007600c0b0380e11300c0c0740c18500c1c480310000c0d03040c2c40b50030300240c0c07254100c0c0780d041d041c034110700444d4540684101c403c64910305d030040c08030420500c22203441d0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 129449046 1250 129447796 129447803
    0x706021305010507030807030b0303160503030f0601080118050408070c0306050405060c270604081507090504060e0a02091906170c04080703031809050106080109050708010528031509 80
    0x3600c9644031401501c542c4150390000e80403840c2440020f001a100b60064892418040d081e0b0b03082c06d82c0304140c04001860003008450640000c400c00490008984606511000919000300d95514241103141484001d207201e10030161910000707018410b40314112103160780d02c044003929159507818180011b280c20745048516000b000040340811015000f940d15070004801c460072400c030b41a41028034807024401c4650840390034040042c0500e0103003d0790701c400d06909012481c600e400303400105403403029000240710f58134041c414010300b440b6a0f18554000359010005a81780c071420002031a240d1180113103280c40c2d0003640c7c0496403030380c8071888049050668103498659154190700444031701680c080ccd805e1a0b130126004001103031044103002094046000031945c0c00d51030303071400010342d4000d820400101e5007403001005507510910650b6171107406840c0c803694650400d000034003040044061200807150080081c64852810a926002036911042d07040381540c45c0caa0107009812864000e5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 129450296 1250 129449046 129449077
    0x611160b04110d0b04050c0d0b0115090e0703020405100f02070b0306040b12010b011103030609040f020d060501091b020c010f08340f020724030b06070c05090606040308040b1608070602 81
    0x307075900e0174075a0b00c45000d951300c000d0050130ae80c2805051104900303180724041c104008850b0004080000400b20b50040100d6a4096540c0c0d08280c03e03c0102c1c14a07100c000200300c640b100d1440e0055020071010182c03200c2c50052903403a290440002d024100460040394000c1040007000a00e074015800303c0380043e020388400751952204020a81ca038001100d1071a0042e40083c001000105d00c01c6440301705a100814012900403d40c842a08495090300b104d6a09a0340701894030011b000c102c50903a85c444284000c01558a188000030709080040d0003090600030004081495084010408070a00600b1580c0503280e0a822003180e0b004101881030340c021480c14039820807824030105180b0f045d110b0000400d10b0344404e882500380000c00f21401002055540d03c0000c0f591303501d103001444814003801c0080c60302810318040006000c0003411261194004000030030004200300b068904880c80400c9498803a45c43c50b0025052410380c200c014001200021894200015035020f051200c0c00d09204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 129451546 1250 129450296 129450313
    0x603050f0105011a04050a0e090a05070329361f14010303050307050a0c12080907093605030708120f15120106030c060c0611160b04110d0b0405 63
    0xa03018505c200e00810350400002d18091000e005041402c40d000300813942107424100068135010300b85011a001142c0844010045992020180f5041c803041500d000c03e488060418203504580c41c000a034801c240c0020a4940c42040008403c03040c10b107800c110b09403420350081d05800840c24540590001c01c0624100150164a0036051024107995242d21064519203c858080c0c1d01a00607004130400c0004031417100300014101d0440c030544e0000e50303c5070301050411840581c20310005030409009140f80c44640446c00301020100619210881c01d44400c01e102d0040500000d0114000a03055110000720303901080000c8000b800301000403054503404e611000c044800344001030b85d400504048091044e5080d10740200c8108081c0b0310200001522079407590b45c06030003506940500046007031420a801071002c8c50142003818210922120710380b4501401182d036004420102078401d2020500040410001880c101d140314001001002135130003501e0030044c5072108a802b1a1203000d0b0a06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 129452796 1250 129451546 129451589
    0xe03040f0801140c180a03110f010201050f220606120210080402031f2901020d021c110709050103110a0603180602030604020f0313060b010f1d040603050f010501 71
    0xf508206800e00b11042d0300c9465035142035085170000701e00000c103000002e001c0c5071281e9680c1b41c548011481035800d50604c6c80d50104209010240414541c156410441042883c5442040d0b241d40883e03108a0640b14009400310302072603e01403000145840e00d00310740030801c84128840d1008140c82120020510925440100e0343d00e201600d00a405910241c010000784020540048240380d120400190320b10442204d9220444a9135000c00f508504e640304803010f50381481800710319029130000f8000b504114401070018500c028842c1c0030003180a00c101e80320788041c80110010712002509010950312420495040d1420041c1d0520a60390680c000502d103020f405245032107111104888038403800c9444201c065030000340026400b95080041c60f518540070b10140d8022a044040c2501c03030304d054a0700b80300300e902840500303060021183e60b01c00595444100101e13124500606a1010003400000c01c0c09400a0b801c010320174094200000a2518158020381c126020200b041c1341d10303500580c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 129454046 1250 129452796 129452801
    0xd0f0203270f0d030506010509060a030501050103061224020403020909030a0f2a0813030b0402090108120d0c0905060403140c010302030105010c03050310090608030408150609070806030f010e03040f0801 89
    0x841540b02500030945803035946010754840d13a03116206041c8645480260000a0354550007403e02101003aa11070062010307507030500c141c001400120310b41c2a103a445948400d92110030183e0049000c070300d050100d150f8402c0301e0b010780d03006641c050300031701312800c00c00b5200c1d40700c1c0c00c038141039400039442460404e0b07103a00c0350307098810600c0e00055041118081d40303180c0c5200d4000318416030743e044c0304102030200808040240c00095000308410312060070548100501c0007010b9100c540c06e980b081c421702e0000000c1d00d003100c0c0003425080001440c4680300300f05584541403940000d03400040820000184404107110306043d040f90f0040d510201f40c49001901280806e001c2c5500290760950782c4000a800b41c402190841255001c076440142d8400e441019174906070483c01c6141c1000c10708200c0d034001000401001c401c814090442840c0c041c000c543d540100528001c204844032001c649582c800303011212842d00e80030001e1000c15101401155254424410b48005040a242c001040d04040c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 129455296 1250 129454046 129454063
    0x3120504091a0a0b030405120d0f060b0a0f050c1203010b0a02010c02010504030e1012020a050406020d05091f0c210e0102070e0a0e0f01060e0a05180a03050d0f020327 73
    0x1444610303154200444200b654000410454540c03041500c1c1c0641c00c81810082c01c00040000c9c808036401d10480310035016101c1a510207543c1c2d03101801030100e07107a000b501d582d50099252600e02e481d0000318a00928007040550210600c2c0000000446e2050829005100e5003a203500280702c98604660200d0072940c00b12400b0700007460300b14a4044600e00032006203031b240d030030b03182080a00054040364800c0340d00c051400300104a000604001154051009075410300c110b0030403034148010078000c04d47d1201422100c0d500020311000c00060380340224540c82000d9004009907212950906103030071200b0700701d848840421209d0980040c01e601c001810800d031340c08150b140c5500d0f142e0041e108081c02d1481c041840b14020054107281c0044244283c500815841002c00c4050402407403c40403100007401441030800001c0b1411038042001400e4680d40c1c1e81441d01d6980c070704840d01160020020714144200c494000400d1144450120b01d40300c07021500444038640c804020070502ea950443d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 129456546 1250 129455296 129455299
    0xa0e03030f0411011218020103060812070f080f070b010e060406080a0206090f102106080c0906151c0b030a030c0314070606080607080105031b06030a0603120504091a 73
    0x110000140002e0700b840f280c070910381c818100541c10004050000007034404005004c52518130390b122040666034940a03c0e80100b44040141c649100ca20890000700e2180100103820302603074103190030802001c841140d6506556a01c487d440701c00710324024605440038413803104400a004082000761409128241c11100b0000040115016981c20700281d50056003600da031041c0c2000803280151141703040062070481955901050100c426154000302d00200784d40245a442c142c0e0900001000042000816200f2228070702250740d041e00040e030300783d035441d482001d1520120b42420b4a80d6510a1b48019a041c6402408042594070526035078140c40c07140074000604200d041c40101c2d00540e8081c5503803e13480a21458484a03442e0075040d5841580f1100070343c0d00180410001c55440b400309805004114040c000f07000301c0b07240c05104440400c2c15203100720742c0040820340f860841d62185008540c8000303040f2801240060280c90740d0414400c0c88040390401d15000e010036403c4882c107500420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 129457796 1250 129456546 129456571
    0x30c02010b010219060905011e051506030604152606150f130212070e180702031c0e100b09070c0f0f05010905010501150e04200f120403080a0e0303 65
    0x2004484040051213850042d500b440c1d0700c045444c049042800b5144d91480400c40c44081040b000702901c08a035001003181800341d01a54501401d59221000c49030000c20840340800d10100e80780314610840d4450340810b111a2a41003c808014403c1680d420031080e8413082c2c072000c1e41c03600358404085201c45034050b84075103500ca4107003142c0f0342500401c007841d50141005007041d050800320488600161064404980e4443c0d40048901e4042d4002c1c0c24a0100e50103000d56007054840a9903034003606905c100080c0c200340c40c4001071440c0780e2125010043c403200301d4260030100c4884000034130f52103400c54001ca504800040c000c07805a040c42c4001355015001195010150300e498400e001e0261003210555210072502c004204e0900031180a8035040095030304d8001c2440000c3c203100c101200da83d00690804142000d440410071654210281089140b540d545060000b88180c0c0b00b0b0010074002c1d500020306000174594840021803040c0d4501c80c0410140c04148001540c0c5c0c002250302141001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 129459046 1250 129457796 129457813
    0x501050c011d241519030602040b070b01051237080415020a1106070606050607120e01020d17040206040302091005030c18060d080c0f0a020312091005070206042301030c02010b0102 79
    0x42170509401034070b845031180e0b500941c03a540c80000380ea00940c0400ca2100011801c0024000f20180e01d03801800119102d0881400d0440200d07186c0c5440d801900c51018010456100500c0300d1410200e001d11003030b80b201c0e0b03402d21490032903610340050241e107180444075050a0740e040d0001400840d8a84c0080e03e45144c5103188081061541c031440086400a8841000081d10340b02c06003d0240c41c3d2003540c00342902c00b00310000600803080c0c4845641154000909008000e4001581261540030580a0b55130760b40c0e280041481441160b0000b900071104e08204400900000021000c2e00d4044054501c030803082d4081200e40820b01c00350095505400c404221036180100c010780f0001e1003031212600740300f80c0c21005403e00308280c1c1c0d26505600400c0382300c0110314050000503642c05a8011441c20a026a0041907060300001031f040107000000926805540d030b101c080c1d030000e10f0030110b0104550400c0d40040b058140d00038099010a050070340c0f002a003070060182c4802a00e040c1c2c000d04015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 129460296 1250 129459046 129459049
    0xc030e0f0703080706090305040504110a02010c02061b031e07090f12031403060a08030a0e030c040e150c090307030f11010f05090423010801020406090b04050108010501050c011d2415 80
    0x520703911b40201c042c004200710002d041d8446018507404480460303603154540e030814a01a003515403907141d46003190400401c102250180c1035a0408060100c108503480383d460320b034004d00c12039081881080030186a410002034aa001030b41c80e0070799001c94001c50344140d517500c50b0a482d90b51410f0040c00704005100c0383e00742d482e00c00091580140014412403001e9901c100d010f007103510140310f400005202c0b181c50352240c142001030b200c0000c41079031304000120465002e1034803860b1a921403d4002212004500d5403130400c0d0076682a07a10080555054590300e00d0000b0308035070304010403074070400950b0300c51aa642c01040b41c50010350b4241ca40c20b14000c0d00108200080048600f070002d40c194086d4402c0340025001d102c4ea0103000d2803400103075600d0a104000d82040c100354014240c0b440104001e002503644410000e0440d9028248241c44806000b0b00d9800f41412806800310001488040384100f000000c800001e00f0786000b0480c0c01c0d0003a001c03108105c80046594140440c28004454583d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 129461546 1250 129460296 129460301
    0x81b0a02130c0309020a180b060304020604060f180e041202030c10050c0408011a0f0607110103230a06090506062a0a0b07110c060c0619060503010c030e0f0703080706 73
    0x1a008146000104c1003030303990001d41c02540c25040384204a1a80e0381c00c545d442004c2c4100250107400b10f030400c2c01c40c58190700182d150321450040500b0014480a1b03e140640142015a403600e62a03d503c1211600c078169014544011502903802d03014010144401c640040111800301000340098064620300f0381100740a00b80182900070f04400410000980b00320a00ca40b004e241000030040126540136810020780d0000303601000c1c401c003010444c840002d0802040c00000000a08001c1f43c019001e14500c021a21030200d005207144214007004581c0029903c52020f51345c01031810046511001c0c144910740c042d0300c1d41c600702254070041607810039000c410241009428101246d0030002d4641e50802107280c00d84e06880800c00440c004401d0743d4082c4a001540003054600303d0400c21803030003180d41e803070001c0d00c804030f40321320303010040080610b641068028050140090001140a050003401010005160503140c094020310503056800800e0313810807240c002c10418107240050700c07240d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 129462796 1250 129461546 129461561
    0x1404050603061009090c02010e070618090b0a030807060504020915100c0503070210180801090b0106050a1418040605090c120709030b01030f03030c030b090115020c0904081b0a0213 79
    0x703100710720314000382c5441a4020003000051b00d03800401c04622004a1070b10f041c41d1743c0c001d0014048803008131a4144d02100c20705c4103d80c1400008a009510427001c81e54140d460b82001d088410005802801e00070240c100b03d000324421f4419540699a14820415124400f1102540220b50b120b02c000c00d54400c0c0100090f05001d08141e03890005207030300003882045111031074008074103c0b49203442c0c04281a045c17000184807950084c0400074050303484898116050103044148400411565801d80c86100e448104203403040c44540c3c3c542d02c02c4d14007100594034541003032045007031010214403070401c008030902429080c2c0c5c10324140034600e00e08054422000741841d0402c2007a210000c080707101c82a200e402140220b440c500d038139003035007401001d0f00c1840c0b06400c241070924030f080641c1d03152158803d04507421041c0080c03030010800000c03810500e05e9411903500c041014107020070301c40480014141003940c0c24280d00084001d0544a0b20b8900d8400041e52150300c40300070030300e114000e4200c1c12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 129464046 1250 129462796 129462829
    0x11805160e0a0e040c08060108010b0109051005090307080615191202012105040b0c0901090317070c0b2802030706231302031e0307080d020f0406050901140405060306 73
    0x1801d043d01c55841d0b698a020880d4203aa100248480c1000103190502c032032409409400c0003409126684030020b80700804901c5001d001340807508607924020310490584040703503002401c2d00c042c19650140c1039641d440580341001c9807101d40707041140a24104400f580074110718680035600c107203410a29501b85901100036414414000c1510341340b0070341c0380780315400052020000a01400c01c1c0c02c203c0400a0020400802510304101080c001da8020301c49030100c80e403007a43c1483c59121910480c9250060360030060110f481c0324004030b130044080028110030f82d00383c28213668400d59040003600041c10b9071f4000c40540c01c02c01034440810081d4002e21541c0b1645900307003103414200c1c2c948601171282100c140f140d26541001031411071a052040014006050b0101000b480c207501407142c50b840b4404006112400c0000c01101340c0610f81c052701d9912181900d85a1995135589020749941c0c0f1140714640010b000101d5070f4800d2603428155070951f03070b025103c64110399424080c001d10340325101d50b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 129465296 1250 129464046 129464059
    0xa020c0705031903020c040207260d02070501060e09011103070e032b030501050402090f19120503040303081f090906060902130302090a0c0c030f0903020612011805160e 74
    0xc10151020000b01d160304081c9200303d0f022090606009007024207051001e80314500410102001c500d0724501d110354204018541016161076604003101c0744911142c40410714004680f21091003410360114089450744440c940e0307103949656902d4225007400100300304202d0140085041e09106541081611201808449507510380503170000c0001c0112128900c03031440c900c0032600041c5e050050b42d0041c81c040e5401d6042c0b06610300014643c640c140903c6001d205261210078605604501c840700a01c542043c007090307000641405501e990240c00700340e02281040c030200e51554185c522003162481e41d801051b08031418075907680d029142c082015580301c0e45401010a40d0380780751008240821321030380c059030154510703c1400f560302c0b80109821845440c2c584d15006281d0444111160070350b1502d40300841040842040d1180c03807690b00b000e0741051010440080c9001010450780c147c5a07480c0b90b0060030003034920824103403030049414480c0e00180a010a030703128001c2e0742118000070001c108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 129466546 1250 129465296 129465299
    0x403180b0d0e190201050f0f1201030803041406010e0402012006010602060114010302090f061b030301030303140a0c020706050a0e0909010b0a1d060d0f0506040302010b040b060703080a020c07 84
    0x2012001c0c0c01004403054426551455140c1490080151070010341e040c0050010082039500003a1607401950000c280c405000100343c0c40c4a44890229240410114040c84495842c4d0511851680080b5011184d0700140401e00c00303074010010308030b41204c4130205032180f5079a1300d078011140400d40701000038130450441780c1900c142d4010300c030707850203448550b0050886601d00034110804100b603055503418103104000080d80380c1c40b146410700c0001410390f10280d4580340c5000794150400c00940801d06c40c0070200c0084201641341e000b41100c4040135111031902e8407030b281d1010440714410032000150f030180c901000500d004802500c000c3c44a414424021b4140c580403442d004011615010565901c07000b0060600d0103404003005400c241d010b003821405a192000f01500010304550b00c50404044000304000703010760b404044903440000e440f05070070240741c041d001e0680b4254803071213142071040510450070700c2c2040d240c43c280c040d0303246405910b941354240c000350b0002c0f588800d0760052960 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 129467796 1250 129466546 129466559
    0x506060f0a050906070f030f140c120315090103030c0605060609100c020406050d030206090d2c040f0c03020c0601140117101a04030506090a081206030a0606080f010506040212040318 80
    0x2c6d00e00006000342c8982901c190350300320082c40c140d11201c2c210304801c028854500d01e01c500090481040032001c1503d0ba8a0700e49002c080b5800306601c003c5035001c80d49500100403d6880300c040780c6064410380c010f20250321000c080181038092510295000700544070041a1244112603d0308400d00140c80002c1042d11036000c10b266903490714042e000b5a0286060280c03580c000c00c081d890280c800d10f098513000c91011030902691100b80660009020568005507075692035500100020070703800c800b007282c0114020b0250182d040940c0d4018503005100000070a000032200b510ba04074016503500201c0c0800306011445207102900f051540619685c01054401c40c2d104581070f00c0b0045d00c161601d407459807500d01e2500c0002084c4100f203400c041c6d01000000e41b01c0c030035514441d282050384c25096031070b000031a01e810035240026145904050000034401c00208222945480620083c0465a10902403006034440d8040401030049006d0014011900c210f49a13030121040c4500240340c20f075200c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 129469046 1250 129467796 129467813
    0xb04090c080304051e01020d120e06070806040c02010605090c0f040305190c09090b01060f110d03020d0b030106050d0b040201050712021006120b0103030806040b040603050f010506060f0a05090607 86
    0x400004107503100240c01d101525091405c030007140390800c1102000294440002d407280c07144d1006005014450540281c402c1c40b907046160b075085100c045468a141c10715004007c1203080c2d410038040e47ca0000c05084842c4180034140c113549003c0c04225078bd441c0d0b9800c00034254030010880c1c0807035a043c080400012418002d41514425058040501e081c1c1c9007040700309050f070b40e801825114078140030200024111600e40341113070050304202400c01161035040d03031108190402000e0354011019410740311038259010f0814040300c0b110400c1990341c1c1c40c0a0600b26082800b41e1036201604070201e80006404548284c0c2c00f510600d01a802e0210039a00c0000d070390801005000540c001036a103100681c440d02c11040109000a81d540b2440c0154a03600078607035042c0001b070204512840010101d40f1503403c90002070001800c1044500d0b56424540c2c2c0381c0820b509030604650030311010030124a01001556103c000a00315a45131442d80e00050b07880d0782c0540710b010b800c04002c2c4501c401140804 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 129470296 1250 129469046 129469049
    0x6010905030a0b071b110d080d09050d020d050f071104110d0603120801060c030e01020c030a05070e07050c070e100f03051c0305130f0507030624050607030804060b04090c 75
    0x4041c40e003544d04102c0c0f0041c162240c03103002c80111903000040100451084840044000d00a50ba01c5101510f00d0504280610888c00502c038103c0c10040b01a04001c00007402c480d0303180e005d6080d0303940402e0103a0308907241d208041118800d05014021b88010610320709200c0000030005100080f81010103100d00b17299040480d50007010f036601e14040090066410114130121514905540158103000340501601040700c0040c081105412601109034000c1001c2c000e0041c0042c2155040c910340d20305159546803034000d0040c4003980340045550503000348147e501e40f4010b90007420741c0509120318440c00c400300a03d0b44094454585001034402c00c12802d60002d9070040000d014002c640e007500c13040034202c40b03807441c1c10546080b0400ca0904000c2c4645000310303030310803884030070480c05003031013803a0160b107406c041d11a40c6024031441c20b24101c88615203000081450fa0307189150b6640070000705002e03004020300440c13400701c00640000c2031070b405416141401400051400643d88401a640146 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 129471546 1250 129470296 129470303
    0x12021201060c060c090f030303021b031b0c1002060408031009020703030906050f04080f0a0203040e070203041d090604060209010c0606030501060914010521030c0a0b010302090a090b010e06010905030a 88
    0x140700344103003c0d81e070281c032500d0a080d040031060186031005405190005110140400d540441c0818261400b188006454001d08044070384489080c12211060407041d99081c4d40c1e4403039107505004505114000340002d2a40340c02034000d96940352070350140c0390700003003040c0c20b10006c01c803020501c280244003404203c4e000303990000e60040d1502c2c01404603040904902070a840307000402c800102c03030030215207a4500d0032014a44841d003004007645503020b5a00140e00c48151f0f2001c00180c942c0c000043c0081300d401c01400030343d480c150301181c01900025260100c03250071410000e4040f6070b25400034101402e0600d00b07042c0c041200d441e60011500650021101c8d42d440e40380800c2640700350302448404107001c4080003030300e500d00700004803d0300030000f0b1000c0845141507200c150040c2401510b15001082040d12419506441c01d50321010090004900c1808540c000c142e09030302070300c03921801c668031841c008096400d2640343e075100f00c8006d080504012046602007501e84050145000c010310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 129472796 1250 129471546 129471557
    0x3020d15090809040c050c120a090806011403012f0a0c02060c0601080609010c02030915040e0103060203061804050c0f0f1003060906050609060415031103040b0403020c040b0307061202120106 84
    0x30102d04100131707036106202c41d404000003840307403240c00e001c00b25036140c0c5600a0710344241e941c82024070581e181082c1d40d210b051540074074400065280344400070341454140460080200043d003804c600c0519174520030025140c0300d26150740d801852114000d140901060500704c2403205140d000443c541d01c08500f05107250004801003100c0202008041d4010228100900c40d840350803200940d030740200c0000a202d829044015821403186104580c0a400449a00b01c11586c40e400d000c07000c5e41c4140c8015004120318080d4882c0c250701101003a009550102c083c088400d042c100300802e1803403403088a0b621610304c240039851030b50b40401441800025403004102c49217001c40103011103100b540441d0054200f0040142266503402c104c0e81601c50300f49a004542c03c070000110300418104501c485614000000c0c4000d00040d02e645500c11031080d8200e480060b01841408196804050041e0b016401000c013402071500038040340d404201304000c01404c1ca907042c0c00e0b2982182c0213900c100c02258 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 129474046 1250 129472796 129472807
    0x180b0a0f020706020f120f040504050702070312020606090c0c011e09060b06070305040b0a02160b0304150902090106030b06071226071b02132d09020a03020d150908 72
    0x98040c0b114800922160000c0c0c0b07500d04581c030805d916070202c9200c0c000c540740c0004801400710724a07002c0e80c014103000781c420012482c0c941406580c0b0f01b81d1303020036540180ca849110120318800146103204941c017030045c5900391507913195842103400480e0b501015549a02d41ca07903404545110059880d4010500454602c600742015411500107000540c00b0700410000b01300402d03044030440f000c5564244c030280d950310804000324200b80c0b52200800181c90083c40004804030703000092750007240580004101031807900e540c1003c0350140c150003504842c0c000d004200090281d1b00a942c040b0001e0411840d1010584d03480c52010000c41d000004180081c40c10384031843c0041960000f40d1000c0c18502c000c0c10038500c040c007030064030301005810480c0043c200d030031074465170a054200c02903cbc5c0140b104d07030701d8048160001140d1400c89600a07032200b1505051400d07e004680e030158018080b03011150447d028403016140902c401c0d142d04d0401c0040440d6200c00f403295400701d5015038200e54542 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 129475296 1250 129474046 129474077
    0x60c0e100519080105102a0c09060605090a0e06010203040e090703050c030303040507090b0a05040f05010e090d1d01050c030316170402100f020f1509070504060312180b0a 75
    0x142c09502c00a401c00005800620403500e41108041a2001c10308008003544c0c4c41c0f501c100560200c01c03104032038241203c590141000594810355055410110060019130344611044a4a00800800700d0f40706c402e80808000c10400840699007000301032042d60315150f100c48814100704404e82d40e2000c254860136081040c00b00a0007480b41042e011405185075003025226942d0310102c0e80280f400c115524081d40c841566840400002403401a100780040c116484d0807000400c5d00340700d82480c480300a400104c8403400400d0f14001103e080c2c03981401c074400740b0090b07206910603e80381814800c1c104217681d000902000a1482461f00b05a0841c44903400c40e8001c00700c82e082d4411040e464000b0302448016580d4030a0340d00300c00824034200040614002d001c03885c0c885007103a00c200c05d0241203940c00004181d850f0251252011070110b5100350b82c0d950a0004aa00710320000c0c00e000512141803006911400001d20100f040c0501e040c51143c03560101042988856111004a8081d0030343d900f50 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 129476546 1250 129475296 129475327
    0xc0f1e06020105040c0b09030109021c050607111002031902040f0303090b134a010b0703050f0a1101020301090b091302010504051c060c08041403031003060c0e1005 72
    0x1809031880244040d040607a940c000d42c1d040350050320b511101c0400c0d005c910741c43c01d600031201941c0060a103001508510742e0b000400440904c1a985400b074200040c036024041e140c1c98409101800c010201e101c40d8000c20002500082c040031011030350149070504002442c005480503084205121020364a50300d0f000d4500350b01039000c0040040284000c41058a01504d184101c440211030b8810610b4508070000c1e002a800b10705110458501e0a604017102c0d2446840c0c003000c0030907220602690b291620b03e01503016404000b80002c82c100b0400c541c101110001d865100341c02e041800004102040450aa81090304644107a581d034800350030b0680303414001550060b00050000d003c080c1c3c80d4000802e10b1045005107409007822104001005d42d502894001c2d054008a00700203a00004500400800d0261010380c1e02c1c8000c40c121b0310000b0360220440e80140d40702040c0816441c55652040f020340348402c884070a10010400300b03000b40e21350702003900381e05074903699003a0f8582e41d41e00300081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 129477796 1250 129476546 129476549
    0xa0308190b01050a0e010e040911010201060501110c19030606061e050712050f040302090c04031403040806010302130608010f0e0d0311032415030a050105090402030303060108040c0f1e 81
    0x840d03420300341c803600c150f40c00400f2034034184850714199400d08480e0780107940912035011000c1e081407804c6406d806101501481e00c0048009a000b40040c941c5e4900441302204928010b0041d60481343e480304c003c0c9441080d40707913154001c0d4243c1011903525102c2c401115190303440400458952480340400704e52030884440641158100941402407035250640c03101d412813200300501c080054601004205541540d0066500500394031262808050f100c01da80c0040c8004c40321151a10000b00d1100c0011040c3c0c2d06036404080105105c2c3e00e0b540801072555800384069403015502e01000c40c40e20800c1c0940c1c103510000e40030106600130000241c0b4640307041012035904040c50a407202d8400d80382c8504480d0869240e51610381c441c042180c04844c171140e00201140d120340c0300b00401d00400c030041c015502c51000c5201c01c1280360790760320500070152011500254160000c02c0003c038503601450300e040e0400d014a1000070f0080d103a00c0e6a180c004440d40040c804100d043c1c6d0700300241e003a0181503c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 129479046 1250 129477796 129477841
    0x2090328050d210e030408031626070f020d0602071110030e1e070b030103030c03090e0f012c1003060f0b030a230a0c1401080f0703020711030a0308 65
    0x584019491080c00f12054103903a042c01c00d54603500b482d0b0404d4020416500600847c6055030f40d01c005c03000841100f000c80420803201c11881900c2e5042043c11654001820565800c80b18a029503039038070080d00c0c81489030201d90200da040303d1a408034000b480039001701840703a40003031a20300103a02000000e13824060740d80b08150400d04280e01e201b2000ca0b0401c0304404c002c1e49090410b04801025007001d134107070030081d0501000300000080c941c8c44600f48600d140651501e11003503071202e0b410003405108540341d0b200504c06070010000c44064900000c08140360701e8880c000700b5848500340d05011400d40340c8401c405402e440c24020f00005220b0700030124813000c010859001e182010039101e6074072040c0648181c000d40401c455041e40c0150b49022055030b42e0030344250540510b48815198102c3c003a111002401410008480d40240c440034003170f032001107000ca0b00e56074120080b8080d42c40204200d5544242c0c8158003004c0d1020404020344602c43d49420140e4582204884e100038642c01c02c81e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 129480296 1250 129479046 129479057
    0x80424020c15190b010203040302120c1201021204080a0e04290301021303081b030a020106062709051302040905030304030206061005120a0b06072003030901050d02090328050d 77
    0x41041d03c8494515020891502004a01d121070140140d081d401540c0c0081e4000c1942c0c41c28a034014408a800b8510388000c95016075480b06101c011801c074011480d100007100a000e0125001c9044040a000c2415144c0790081750016014085015105d44107140340309054102c044200c02410054018001d2a0640085041c00d403c0c81040201e40300d80d10000e81030140000e85030141d0120401e0306401081c00c1003c0300c0e80d821030f01e80028001e0900d489510f00042c520007000f8210b042c8a0040341107240c201c0d105e488881d08140410004020141500390804101c100c01c1006884500451820501503005075480f0310301810045c0c10010014001e9108418080c0030481c43d5030450245c1e0042e12031007641c10b1607070b0b41d000c15910041020a8846901040114410040140c01c072503440f00760742c00d4425001115414000d142e81c0e4003a02d42c64601042c002d029201c0d6005040c0d002c0c0c00c0c0c2910050480d01d440a03003198840c1d0800d80d9040000d038048954600710b00f0f00104103c03002c4501d50a1901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 129481546 1250 129480296 129480301
    0xd050a0518070506091801080d090f0303120507030b0a09140a06030c03030c02030a02040e030a020f060606041406160804090b0307050d0323030c12010509040f03080424020c15 77
    0x142a00d0b0050b500902e8813614022860104079141e160499081d0b0602040399101c1b07584401c08141d807517801c00000d40c0007402c1a080803035104440e400410032658181c0f2190351035a01100e1920250000a00360001c040e40c5034070ba44069910b100f03692004100c05440024068030040d5042d5150000400c02082c81e400c0820400000300100f0b8010100c075014540020051030301e100207420030006c41c002075400b0303043c0754811085441c040010306410505408490005030075402292300e40b58101c40203588690706000030402a4288410340e9089000284801d141c25150403100c1d40d291910501134500b0f07000850300344070301c0075240304081d049142100280b401030f2801300010100c14505200404001c0c00aa08078182c5513140d903007140303807180c00010304d4603444c110644a0440d006000809002c0005400019042c1086291a405981c00c001d041a12a200362810b440395207000d070084500328941241d0740b00c00c050026080440a007140000760740c80c00c000032607515220442a140640d103040909 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 129482796 1250 129481546 129481591
    0x1e0501090e07150905041103090f010605010e100221090a0e0405030a0509060d0608010b04060e0105091b0c070303020c0f04150e100909080a030606020609030f0f09060d050a05 77
    0x10100c0c00c5a40f4110080c02e902503000c000c0316a05000c1e40402d8025040c4000b28038008514406103206000c0c0c04112400d052080110f1801c0c0c42c014445c02e4003240d00b12005001c41d041c01c888102c03c00c180c50040354000032011510101c24400405031a40510340450350341c101e0b02c2c250760181c004000c0351207405110f081c00e842e40c0f6140e00c00c00701c1d500c00b0311400007001c94054445e0015a84181c000e844200105565003040b14068480f2080d5548120310300080440c000b032000c5400341c1a04c0c809401d2007815a15010207200680c285401203405904c24400300d08198020804000610b20941c05400300026400030311812141200302d0a100c2c0d801d01c140c3c0c1c0030000c20340a880e4101c40320b201380302d81c058944840d4046006401d4000701c0380c1c6410a66904203100500c0d0082030200400d98040084555440d802c82c0c0340c410581c2c034000d031608100076011140143c40c1c09402c03991400e025003803800c0090000988143d200300c03040b0500645600030851200854032903d50302c02a00a4052620201c00e0b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 129484046 1250 129482796 129482803
    0xb0103051c2606010c050d02100b060a05090f010302040305070305070e0a020315101101021b07060c030206130c05060304030f030b0301020a020c1e060c070f06050f0d09020111011e0501090e 83
    0x600310080c0b03440c000140c00b0340e01c501d070f0500500360001c0568140c5a103554000303444542c00381e00380e01a9410312503030f400d00f41442c5088507031880d29907807858208a032f900d0800001580041010b41010303024403007c00418400c0c450303480210b00c1200104200c0d49054a80411080000d000d407489a106004109565421003481c01c2e80c03030302c00c81d8066269220300c80c0694904041005410842d071010070342c40030302c0100d6013502a41102a408a411b0565900300895820102220080068120001151860400300009801d981c86481c508074910380f10382c08266141c00449054000910f40112211400e07054895407981c3c480c1503000350300e00b401c0c8840196841840da00c0440c000c44400501c2c3c01104110300b0401031050008220f1035441842a403c03030f50b240198002d500010204400009405009008848459540162090502610b070742c3d000d009244040090341446281c19a005002e0390a2080460329041120100c4140030003041c00c4044441c140c2140c040075180c41c04490381a0b0001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 129485296 1250 129484046 129484097
    0x7080406111603081e160908072628020405060906010806010c1401020a0224011809110d0c08010e1501090513080409050a0c0318020f04090b0103051c 66
    0x142000b41c01c5440b000724080401d4050691980001142030034040885406030807110055004e5031f600360040c2d16900090f440d501c3c10303c100703184280180002a40a01c030103031111564071880c400d440ea4148100e291000c0307000b41c41401c1d20414107503c41c0302c0c11494248205d0742c0201080c0d038002814503003840060020400a008641400a00d285400c1003001d00084c50b416060020001d64444207480b2002c0d42e2841c8104102c8084189082c100d82d150750510007840c1200e15641d0a4600441040f85110040604050076511800c03040400303903e5480c0c0c0008004040d214054030a100e915203c4000c0c2100c02c0b8004411072900101210001101022107003415100660303c005059180e03140321844001002d14001d00040000c203002420b000d850340722600c2500b4101040c0300707410480404800301c0d400c6103803100c064549107440c1c4016081003407218102400c0079100144c0c00c0d00c20745507840d040109034012103040e4000b4007c20b04549140f24012111015800d07d04040b000a0003c42e400c103084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 129486546 1250 129485296 129485303
    0x302031b030304050a02090c0903160302040c023409051314032809050d03020a1a06060a030f060f030f02150a0c03030b06040308030103120801081c05030c0c0105070804061116 77
    0x2210041913202d501e48d012a9000c09004003194000060100d04a0b00e11402d440180e03c039034505418151401d0000c00c88400c412001e840054201e10300190002c00c00700400000b045404000b2004245040c8602c241c078065039100303440030521004e41c60f04020801320704400c0b55040d00184100351800304820010142c0b02604031032201c0c181180ca01c2203502c1016540250760010035540d0010505401040c1403890038014011030440c030204c0c1c04014000030f821360ba400d4111030300304106040e00703219502500e403034800d5580120381c8954889000300101c285400c20707103072a904c2405a208520f00111003034081800f00d110282400c1c1b02c0d100141000c0d50b205000360505482d2648644566500012100959442078000380c40756104d09081078042c64250a40000c14000710010400d1100001e64403d01d403d1001200c40204441e2001c5860340c00c0034200e940c10842c01c2c0901069107500303001d850310600b07607603541521031b1400c2c1c1400c001f6108008042c19440404104030150002e12099065203281c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 129487796 1250 129486546 129486559
    0x905090901090c0e04110103090b060111120c03180a030b19021c02040602010c180b09010903020d060b09010f05090a020304140106080c03070801020c250f030302031b030304050a02 79
    0x440140040c058200348000903c0908280782c080f41407948402c029008602a28001c8880f605000040d8200e583c03000000c0c1400a1040015406612821600c40306445200581d42d080c3c0c41a0340102a0340c111040a0140e9000490344440408c4441750301c007030314601102c0e800c04403071540d1240340c0c0b03080001d4124a03190442d45001030040079181c040b1200c143c0c903450710500c040c40500483c0029085409070a00650030722000c0d1520a2050b00080c0a0701c1d05440070901031441c0103115020b950140003460b060002088002000d03903220520041200d015030300104855169404001c25400140c100460038030384101d042c44181c841c080c0300b545c0a8484940160360fa2200e01b46900034001084820303400350b0a00e02d010520f06c82c0443c80840c035800990866489d1500d800c02a4282c0c00f030b9000021040d807202c02c1741c4820400380552480f0348030b0007496081e8a26264000380701d840c0c040350415170250b070000509d100b48080d0304c000e4601210680d00a1421424107661b442e49484030f4000180c0f0410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 129489046 1250 129487796 129487801
    0xf01020913020c0f03030106120b0102010b130c030b06030a060609050607110d080708071401050c07020609040c090b0c0705031c050909071808060f0604050f040b10030b130c0f06090509 81
    0xa001c00001e13000c0c01c004000c0701d840e503a584000402c900208256904e1050800c0c0112219500500580710510b070000d0028440e031b180c40002350300400c4200b00c52410907880750b500048540b58a801980200360102c8007140321807c0400c05003031008680d01960103aa000c0000b0004941d0f0b040d002a04a501218121480642814052081d0044d8180980310000002b401010440401c011002000a400080c0030750342c0e4102528500340103640001c1d40102c0b0401c0540190b00e45a4005888005142000c0b1580c1ea16a20b59140030f070010446000030303a00480b81403010346030804c014907a488404840003000043c101d001403090240000ca6070040c02d40c00c02040c0000d0003003040204100d5041b80e01201d0301d03925400e1958030740342540c0d161900403d0a021451504050066500c924503c00200c661a00d9039902d12811282c0140014a443c0320428044000b681e414541e5020744000242c1c00750004685c180030322000402c3d4080003101c5070244003000038a42004441c3c0458000b16103054041c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 129490296 1250 129489046 129489067
    0x5071109060a09050411041109030705091b0d020c06100e0c07031d0409060e03070b010b0903060402090a11031003021009030c06050c0307050106062601061e022406030f0102091302 79
    0x803400307544680d41c0b040c01c2c2583c0048c1d80380d454010f41b9031110105e0440d80c04a5a44007030140001041d244244d80480f00022a401070585000414042e03004542c014500b403416140d80e800e0210a075060f50340c0081081e8108812002a51820380101003030455900c0c1c2405503402070042c914180102010250070a03400350203585a0b0b000402035908100709000c40e900e1050220b49039800880115491091080042650400c00c400e44808000c05030052050783c42d582c0070030000c200c0090583c4906619400150340795100d07a8080c40c00381d0301040c11918a5410340c410442e030030462540b0001048560b160030000710741c1c0401c140003110002d0408540e211034141c00366045100341c1101410325130900300000f440c60760102003c3d41221100688a41545071130095200c1c143d0288911800120a035840b0f070b9584150301d001d080718100ca03004603a07500e0100c103a0141c030001000146030b00c0581318010000507080c14002c042c1e48100b448021403500340c6c1040001e002d1008401001c076410360108012408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 129491546 1250 129490296 129490313
    0x5060703080618040605070207080304080706140f0f0a110c0102100c020f24181002130306050411011404050a0b030a150b18040b010e131b05071109060a090504 70
    0x31050110b403e01074134078060808070040e100036141000144a020800684081c010040d141075401c040060461546480f500f2038115030303070310005400c9800407c1300c24800a1681d00512081e0b55843c0101d448003181d01010700300401032900003075503400036045440780f41e030b001c1103101c80c1207482c110000e03003040d5013641280b41c841c02c112030850a02c10440160070301205150345c41c044043c01d910980d400d9480110b15040c1c40380c155491041030340401e02307102030054680c0242c50009030b41d003a1074054030b5803a00c959050300c800b07a40c140c03000c000141707004a065900924140b00551003913411850140360001094940002d841035891001c40400451f08440031030f04540341c0e100c05002d11400290f2109911041035000300d48051052581c031085022030b090a0090107040c203c140c598100c4040014184400810391940c0b02c0c404941e101350040d400c4c10542d141280f0b07401d040c1e646684409241c50700c089002800d040309885900aa001c000f5035903100d02c282c00035148510350100781a03e0360f107410202d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 129492796 1250 129491546 129491569
    0xf050a050c07200d03030b04050c0f07172703071a0904110d0507020601140306073002030901020703030e120301060f050408070e040516180b0a0905040b0f0709050607030806 76
    0x140080413035140402e02d40d16400002c0c0c818400c8a04001d07a48803c060803c1a10861203049150303c01446804d004c50f5001c5628105000c504d0312142c07404980f40340d000320148140042c410004031213120f550041c2020011540a480780380c0380300c01c0d81d484403940850140034203010a07102c2c588075034903100a200d02009a400e43c1d1201c000070722aa0518010284d02e4a800b401042c040007226040075505150000311240500b040ba1580c06013008008400000091440c0e2003420701c40314003402503d4000503200440c407420900c000107866490340c0ca07004042d104050180d81e079651003420490021803520701128111651402c20740c01c00010391006980c140607035400945103014103070000072260303c4e000130180b103944a01c042c1d0b0b68800d20010101819000f40c0611404400e041001c00c61140b882c1d07100088a80005050180042c2d031500f034101590b100720b03000c444503005542442050940704c00000e4025440c0c1c2071000348242480c0202d0341901440b20094100945480440c081e500c6501c074410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 129494046 1250 129492796 129492799
    0x90406050a08060106170402010503010e1e0f090f1c0e0d0c0e0402010f18171608030d0606020303131104020c0a050f0f01060f030b0c040b0408010f050a050c0720 71
    0x402480d42c0c0d0b102c4580380e03442441040301143e11b40ca03803583e00313030500880329108070760585078079003140d00300f500600f034558006001500d5481103c00c1c108145860408040c842e444a0801100d02c0c41c003a00090304090603040006c0c455401301c1e58034400428085e9200b0204080c1d868814484002c01340040c00358201c9220180c040e000b220300100f9a103241041d07142c4118001c5e2a01c0c4448031904004030f8000c02c0c0d210006e0b5125075201c405101c000d41100064010034102030440d0146548481d94010800340f59004102c2a40300240400c0f40d40c0c800c0c0200002060301d40095410b51611054204d808404d000000344940710401441040d036946605440903c403850049499511746840d00c6642c407000c0c40008001c500c5600c5008847d10014024102641c6100501000d414039503910070144842c05004d02102000a0101080109144014200174070340c84001103290070f8022281000c0316809000c4c01501c0341890100130382120030f041242c0281b540300d032005401102c1002c0d2a8ac0080000c40060b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 129495296 1250 129494046 129494059
    0x106060e060a080c0a051c0603060b0a080613210c0b06150307030e011401080c010e0a05060f0c010b030a05100c0806010f0c0c0b030c0909090a030807080411060406121b02030f09040605 81
    0x2102d05601c23070b8024801d40344107120421036009940104544064103202d00c00740d5034818000584250980540c114401e0b118005030348a80181c4100b141d02d0074590244000040c00100b600c1003401070402e60075800c03540c00e884401d0413101d140c00f8819140700c0104a10141512002d440c03080407002d41c810301c1d000116241000c01545c4488442c0e2715010440c0c0c0d060300090000440d200c1c145059540c1c80c04946d0000c202d54504520940141c51981118085c1001f81d50b130346c10301d540d0540f018043c1e0b1104901c02c1c809083c110f4807801c010f40c02c80f01504444820000070b1010028183d8001c0e02c524441162070400c1061460545456500710030150417695482d080801409040301702100507082c010b9080324821410354810304895590031403030384080c000070200400b04641c1070180f2012074119000300d42c500b10013218100814100d0f4002c0c0e01c020001021b5080603042d0298511850204201d00d11852512a101100003940c0740100341001d00c4482d00040d044203140d9860b48900000c0c0000f4154 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 129496402 1106 129495296 129495337
    0xb03030a0e04020c0f070305060702010b030c131b091701110f071b03051006140a030213020d150305150f0103080304230106060e060a080c0a05 63
    0x1a50083d07800c01102521400502c100c036031400e60321009005652031481d1461400000500031402c591500307207030f035001d40c0e4040f650300c001c80e4044131079604144141e2600d41c000d01984490f041003001001d101280150082c0d034400403107080c8d03d090054003c0c1b6a25032400d0fa00303040d00354000140308000a0112101e40030162250a001c0e80348540711412505e030310f101c064155042030b034282c0c0c02118100890b22140c01400045e01e00400360321281841030011030b080300c100340002446064809810707441d4030404d5040d41d4003032250400c24008440004c0e04040445d4460000362041c0c090380f02440c0400c5051450359003e500c100000140310303031850f12050103a410107441100c261400a140d0030503a9111010324800385900800065114540a4082c00703041c0b000c03000318040e4a00344030200e145a04880100c1d031003078509000c1640c0b42c0000c03c088a10b4811814008034240800b05c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 129316546 129496402 := by
  have h0 := BRFrame.cov_init 129316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 129316546 ≤ n) (h2 : n < 129496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
