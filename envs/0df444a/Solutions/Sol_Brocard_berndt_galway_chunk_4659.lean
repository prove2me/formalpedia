-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4659
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:19:39.895285+00:00
-- url     : https://prove2.me/submissions/c30149d0-eac6-40c8-a999-1e3bb0fb0704

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 837769784 ≤ n < 837949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 837771034 1250 837769784 837769787
    0x2304080f0a0f03030b01031805032a030d0b0a050910030c120b0f0702070915050a14031c030e06070f02060604061a0a020102070c0608010303271a120a020c010c 70
    0x140c140030b07002401d0180500503030f02c0c254040e080c020600740c105982c03107440b036203c00002d240325240c0301d02c07500c0510750318800c0403031485044401c10b440c040b240c841e8a0389000301c418004200c441e6001d010301c01181c142c1510002603600e41046d80455004403600d070800c110380b900c0302d136010180c038403444a00702020f45030840b4500354080407000070102900907010515841c540c1001d198062074510444648985549254060300d030728030366a40b94407011031030610092604031400b02c00381c129400400990044240041c1d0b5030003496100059040300009108116807280d04445c0c1815522011150303941080000108140c07108100b180050040401103025883d20380641d90072120908060a401c15245440c00703245d501c800c2402c000d5646c200166000192108d1000c4005c04850300c900c0c0c020345c1f440c200504514504400307070044064a03804101c0c04c1105030749000507560041020740134041400f190340000e1013410303140b00b0a00480003c01210800c29001000885000c030000d00c404003a41a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 837772284 1250 837771034 837771043
    0x30207060c08092e030e0c090f280c05130501170411061b1e030301030b1909151d010204060c080708160b0103060606050405100f2304080f 61
    0x7801072802d1010000e900320b0b0714004400c10302c8200e80207880b4080c403401c84001000c4070140702c18000401c5d01c460984503900c40501044421081c15105d80d01c66103000c4800540c64a0003c1a022840745114160409068a205040f65164594600300102000d00700e000d0203541181d4403082401c9116000820309500c074868101c03141d55402c030800515100d5030b50700300e042115007541d55000303041440b145409007040c48481e040242044068541180300010440c040139940801030095802000100005115800001d600507482c03000c0120049070b940701100a01130640c00507103062691354503054503080716440b161000751243d02600780180e0741041c903803d0b40210f1240b03d020036080c03e081d101051942004215980c8140d42181c0381070894202000f0001d41918150380c0710003100c3c014401c01c2018440c06010b4641401c20a041510b040c001a01004072910300c5020480c41a921440050042401401004005504d684078498007114401590001d00c2454200e109501c0b451241d03803030108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 837773534 1250 837772284 837772307
    0x91101050f0a030f02210114030609030a03050712020d0518190605041a01060203071a10030219080d0c11060301080c090903120106170702160603111b0a03020706 71
    0x5441e40d080030308944040c1c0050070b03403d2024907401d400700482c0e003020010f20607002c28101c0700005440c0c594100700141107887c0188082500079400f030b0307080c400d24030000016507d5600c03291802080980c0c0380744044582c4611000030960090003c02c4440d4070201c240c001505c9000c100d01400e0407100010a1281d443c4a1003a061280240c0700403150702007080b540119620501504078020f0210615002d55081134090f800400141c0001c1404005c108040c0400504201c0d440d80e4404075041c080c00301c011080d05840300030b218455014035440078036111001600281509010340301c4070141c1e50405040b0b4106c040003160311811071030004400e490b140043d41d050b2075441008095822164081c08a00140584010b8980c40301b403042010b450030b0801994080e0425a440a44020200b0110744140601528600942d0480107000755403420700b441800131a2424900410f034810300c1c0c0301c9000b1a2145550602c80100c42201e802c8148000007403103510030344a60b084620580c0e5411007250745081c6071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 837774784 1250 837773534 837773557
    0x30e01080c030123030f060702060708151c05010501080c0a090207052112010801140105040203040f0b13020301093e010c0206160609210215091501030609110105 71
    0x240010302800d951682d99001d040c8000202500500c5004002486d010b00703400149981e03030048007080840b0307506010b4240c0203121030a00440390300302031343e1400c0c410003465242c2d4003a03107620340019052401004035a0000d03400038004c001558607000c10545071461420980d006100500c1c000482c044c0c01e00c2114400d680180103071614103040c03511240704c4140b03590358606003c003d1044180300018600f416000308a00300000901800b844150010008140d001b54030a91040c4100000308903601d840101a0b6400350303441155607500c08040003001c102d1074020f5015880e1449030010829980b50100c4440e002d2900b00d65841d910780d00c0c050000b400600918580315000c0300c1030f40c0301e502420b0500c003d6803006011074203007100446160390141802205854058031010000b044c0b1a4100102c150101d400003040100041404e01940d14083e5040303524000c8800d81c009a5058010300805441a40406858030341e565a41008406440400e4043e60158000071070440d10b076000390100c0c0c4010108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 837776034 1250 837774784 837774787
    0x60c05181215090606010e01091404050703021303050c090907050109030f171c0c0302130e0a09120816020105062116120605010f0509013f030e01080c 66
    0x9001407110a860304648100540b00d2003920200c0e5000703618042d4070074060070b001056245000000180701c1c0e600100318a0600103120000d120b00515003000d85c403000ca041e9000b02d190b4a584004400a228600040c01c8000f126100072041103008909402e0f20f62003251184a2500c846480903100c101c6886582e01007a248035007080095081000c0d41d00c8907014850580ba2040103103013441a96002c6459104008080f0307111005c000180d00c180c20740c002c89440c0841c18110180305881c0c40032070500480808001c0d150000340039056942202d00c8070340d4069401c1c00721060b1000e000d0601a42035501416480c209030708072585d640305114441c41418010801100000701848162180c400008004000e0140207401500b03d10058242c03402040412280800c058007410094111841070f0055040559541d00030807c82e46c82075412030640f1503002d58450600d02c049100201e14440350600042e12411181c1400207204c4c03000c0e040901c9010340c9070403020386541d10044a42020403204400e10f040f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 837777284 1250 837776034 837776077
    0xa0204050904140102120a0506031c0210110409231b1905090316050a0b0313020f060715140c0a140a020f120d0c050c07050405070903060e0604060c05 66
    0x2105603d0302101c41e8850006141c0840c8600e855103900c0115881c454090b1105d0600030903050401c500c1d820640f21983c100a81038140800a4131001007003501e0301c0c0543c8030080402c801000108940c02000c040c1c1c0200301c0f5510b4031842e44508400707654000d0a2032480400a80c1e21500151070071440d0140d50840c034644419210800b000c0d02400d182c0c101080024040300c0c02c652402c20000401c080200321000c4050314080c1004240b49240d0015040e00e20188107104e003208840480c0c0035a251b044421154010303000300410041c2c00764240103018000702c04040440c1082c01c1c0d10051035004204400c1c0d00d1750b511602101b040d44100210400050a60038a0010003000c10b0064070b902d1600e072068030b400101514241d8500780081214408ae4100010910280050b52145805044003420802d040c040110800e98079907003644600c074016910f410004072854440c07907105028680c80082040070a510300c0285507110400c99044804900e04040162024064000d60340c8003104106200000007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 837778534 1250 837777284 837777293
    0xc0303040204090c09050a0f0c0201091a070c120c03030f14070e040e0307110a08010603021003020f0405090718060e0a03060e010912081b0403121b0210030e060a0204050904 76
    0x21002a064030490000000401c281d00c07030b40507982c02481404004201034140300256030427159103c9588081d03a14000c003c4002529851464a2030031820140c014a6642e05605a507001400f010041065101243c0b0076806070708a4400d8285a0085e50704001d018238200c0c3c406c0c210b0f545903c2c580a9112020000b82c3d101e803051142c0081c050004e00301050000c0300265541c81c50b041080b00719841001d098504010307007015001c940013814004028025145960045440d4400c1d1080c01400c054000030301c00b91144141d01110024140641010725500d001d12000340070a031b40e0340e141051801526800500544030307240400b13075408020100c40d1000d00c0d542e1854005d002e0350f100c802d4031f0354031400704001142c40c60a2505154a00781c0b13134a03210703203024139254024580c500441c900c1c03400c0511050000c901c40000c510540c84690800008500e01c0f141030130f86254180320000e52101c8203843c4000e00b29495084110050607031400c40d07030307103440380c6103c00c080c1d02840c0542600000400002070104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 837779784 1250 837778534 837778541
    0xc21041d060a0f06020c010e1c080309010b1509010305071d0105090301140705091903120c03111f0b060f07080708041d01051c0c050f130e0c01030c02030c0303040204 73
    0xa04020076400007183e0b1000764606071400c0d03030310090160f00f00054410865030071036061004401c044440b00c1c0344000c40b11211070082d08000004c0c3c035030180400041c2080c8000d51041101d0f0000030844910714103100c410b42c9103070340124a0a400a800d090205070360f540101e81c4500324408111600246000600046650b07030041035076950715649401c000748012078000710f214040d201550317420741e0710b141e6182030000c10000d21524480c4801c0300c41c0c0800c042689441c881211011502d013000c007000b50b9040c2100e10340c860345082c901d24044c01904081c940410710115020072540001071250f50088800c000a50080410f82e45282804120450014001e00c00034410240308901032420584c683e00c5c074806082510302c14155a520300b4006000b82d19205491180e143c001a4419544008695920701d45101501c2501c1c002c8410301c40420f82070360ba10708880c82d00c4c2c581320000c0008444034100c1d203603107800c6c03101c42a0129190421240110b440441181d054600c540c0096140da1502e0b402e11008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 837781034 1250 837779784 837779791
    0x7050a09031e030905010f0206010b1602061b07350f03031008160518090309032b08010518061c0b0601090f12030806040e030c21041d 59
    0x1004241036001c000101400320001800c58100030341c00c042142442d01412a1140e07400150503c00c0c9451958041540014642c0c150741002c021303261659514a5442d46044d145500294084404607809400406002002c051035419108940c0200d54610040c4000280200720401440008151130f510f0350303c0341601000c195900c02201c018140c940106811034005841590341e003a5003010421036400e08004280c850071183c683e586034a46082c0006842c05040ba1030404042103020010741e1901e024000d41e0300b00d9001900707480b0a036070401303041200286003020110409031100b450707155945c2315a06444c10b84c2d9002e001325a40b0040180014101700300240420b030704c0740c841c00501202e87d000c0070b211000c1b54480c5a0b20300050402c400098542511034021701e4410300c2c0c40703d08000c40074811030031a400903094105500242c43d0304000c10090003013a4455080da10001510060040780002d45002005240c00000c0c00180ca0308200f04151050b441030004c0450300085600c03a66004242c40340c2c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 837782284 1250 837781034 837781037
    0x13203070306050c0a021204050109050d0215041707090507080c07060e4c0b06070b100e011401120e030c1c020705180a0914010e010203150d02030607050a 68
    0x2a40c565a0ba902002d58801310b0310441c92040204169907107680401000180031030141d2454140780c00e01e4002000101c0512a291003103482041039000d40d140c5107103519044002c8100d05a0b181d848280458010385c401e0329500440c401c0400010b800700c3e031841840c0c0900d06650320312040c0d8a0700e0301803980e00c0d04a10310940f1041e03610302c000e4031000d1003046001099034080e4a4174280320742280c410100700b00c8488212180b0741e40e015070f1641083d0b404105000d000300b050b1000406042001c007007040e0b4000d07003d00604040c00c3c4010b1001500c41420311307008460400040c00500ea032030b010441d118407c0ea4030b0050109512264903102d58405400507041d02ca5181d0489080c651455410380ca0400300c0c8690840341800f1500f130140c11507051000c030015110548805415002010f6416001840100008000e5542d54186400c000d2001c1050000140c0c0340f000340714403251590124000c2d0310584074400444041862503c1c3c50400448030b64015070020302501b2a40d5600f0420385150f40003220000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 837783534 1250 837782284 837782293
    0x3020d022209050615041e050c04090510090c020a0c091e1a12030c03040b0a05040803040603020c2107060518010204030b09070911041401021e030d05013203 69
    0x50201d20a03105409000340030710000c010900744454032080e0301404071340f5903004034200102c1c58044014a905902c2c00340f882540028150f0700c03c1c45501c0c2c0c50280da00002c2089003400103102d52103400c00c40d40c100b551910082000780307000098003a030f5110442040100860000c1e03408001003a00c42c0d000c0190480c0701e44140d401d00c08403041e00780c21150880b003590215240981c2013159170800da0100784841082c900114a000140079a41c0c0d43e034003a610400c00e10b01400150902c60340c0c030074021b4400511000c000c0320f8445031224006400f0350440301080199110302c0d0455901141c0a486e4012448202181d0174680b004945403280074000c0204003001380b134201da5103070b44d000380309200030700c0294001c000115035820801c401e60b0415160b944410750b06030428100100d0284650211130480700c0200440c1c1800900200503814002d20101600c00c89000c010513100be903401100030004888680300802050b078851441881d6041034644820420581e041c8034031000628810b40310aa640060445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 837784784 1250 837783534 837783589
    0x100e06041e080d0f0501050105090303071b0f06021b0a050a03080304020f1903060b0d12110a05060a1d0106140f0f04020a02010605150a0c0b0a020705010c08071803020d02 75
    0x60b401c543c00004001540c607a6414581c0711402c1d1845000d02406007460500e26042c00e900010f075a03402002c0b009800d200640942e4800303c0c0284246500a03c1030403032a1a80c19501e110203521244031100e04003601d59018003084081c0741800118094a0005103002d040f00c2c1540c48922050304000c0080340c0000d20502c0d10142c658404102c0d4541c404e445c3e501601850461800105990440032105c1c0654401413803c0c0c00224034041c0c0c000041504d207028a454020304d03090900d80621900040c01e03a0040c2000d001c0d00e103000740c115031401102240b43c0c8801c01a032078011801c0310307240c0c1716041c0c4102d4011076079445403400036040032508000174a49a1007003180800a401c1717900a03c030040150395100340401c0b40d03041c40b409000c40b800188024030f05201b006c90010b00138080c4094010548800d0400040642d0000e906807240c064000000300100000004040c050395810385980d404642c0c80003100d1442260204c1c920b06580e80075008240800c800d0f030030302030903a049030304000c815407491860 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 837786034 1250 837784784 837784793
    0x91c0c24030c140304110a150908030405060313051218010806030604030206010e0601050f040f03110117010b073008062704032109020a0509070206070f0e0a080f100e06041e 76
    0x30700302a1083e040ca0519284008c0400741600c103059021400f960410b10040020b0341d01c1d1019294002c810903151000420545407131800d00707039800c00e040290040803c3e01c0248062030141000c4400c000e0b200c0003003603243e140c00c0540d5010119001401a813000c0c0050080405181c000b030740000c0d043c1072407820907008074440f16103a00700781c111000c0913030302c20406c01c107000d043c4101c200e6044003800d02d29035003d6000761103040c5038414012460000400070300c0350100804040389503d60315801b04002104a00c00307000300000942401c40d6000030300c000000c96200d10380b54626121714107031030700c050380c9451002d426152800c400600580034043c030502a40d115882d004151980a180c0c007400141680c21031040007041c041c030b41c12103070048807044d0412580380d030000b0b5501e81012090602e01c565003806042110200c0880c0325a0342c00224140c3c000480060020342c03c4401d40c1410241c1c1c0001c00001d0b40e10b0203c034200030b0704401a41c00a404900031070405242c1c00b4010070507103c1492200015103d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 837787284 1250 837786034 837786049
    0x12060506071239060f0603030c06020304020105090d1202100515010c0c0503012c0109080f130f0807030209090d02060f0a0e03130311100203091c0c24030c14030411 72
    0x2240f040074040a40c08081242501c100315081c143d030242003100a0841c0c400410208448030018241c96000011070150780c0640141d41c03400b40001c100c008c40000900d000c0d101e5001c84070155016100300d1103140c1c1d408405008a82c850031813584042e160301020801112003003009134042d60a0891f1090201d110b803800e0048101000d5044522414100c0109034107001c80e080c1005001c40340d15141c040030006001004840301542c9907116151070301c22844100081822560000005410482c0c0c009592500403441e102101d00840e10300c1810f03a02e094282c3d444030050807105005821690000b41140003074451150045070b0003100003101d501035400e052030755110400074000e042c0e90280030070410140740e2000e00441c41c01e84103141034440c2c8200c065520f01440701214403038082e030b0810003100c0c0200c1094403e0f0a82102100340c180d561000880c981030038034642c4d503070b80810303401900410034040e00901c8042d11031030380ca9407800c032591260300f41c0580000e44116044c800d0701c80d030000195034192 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 837788534 1250 837787284 837787367
    0x90105070605131703010e0115031b020714091e040f0b040f021215010603020313020d110f101403190507080708011406090d03110d120605060712 64
    0x1070483c0d88004880c100070041991400703116120001c00c1005000c041440d07600716044a0030340d010a03004014010b41640a400ca004441c3c0001054100f0b6200d016400201c800865013031130400c00221404109100300484111000040d0110010807003004500c00784000d40e01c98007403802c4031102d0360700e540c0308800c40308190340540701d5621307050030309003076240040304284010441401000896110107064882d01c4051203002d01380355010000400c1207204a54060455900612903516202e4074580b0781c449101800c5620300030008545410010b08008000c000c0c00c440c06c1d00c50307500300d0700104a000d09640c8010846c03018038114419070400341c0d4060168034010f031030549440340989441c0e03c00808202c0168082c07091104a00c5401e15642c6681702101e510a8081d12942d090508a04040d16801c0c440d0000200c07a118800c0b614140b254429a03920441002090a110299035041003041d00d00030307040040c002e840103c085100031402039002c000c0c1b030044421285400c03803014600e040c040c8040b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 837789784 1250 837788534 837788551
    0x812130b0301091506050322020f04111215061606060b0703030e0d0e0d080f1b0307050d020109020f01080a0b0618190305060c030c09131b0c0215090105070605 70
    0x404022080007000340110005c0c005900d881402c61815400400c000481c8221000301c5550302020b6201359243e0a80b0722081000c0a48180051800040d01e6011580311260140c1061000c1c0d0200c0c5c0880c0c4102c40010116200070002803c00002c8403490302801d025510840c2d00588e03c1c0000078041c6020800307081000d010b614009800510290300c1410400000c40303100400440e901085460380d01c0011440400d500f01034241c2d102d01d110750b143c5a1078170138810381101640e80f0070340c0c2e100d07125030000061101500c40c1d01070760081c04019800340e00b62064202e000794442264141c0700c510b03500c03035521554400f19005c2d02007003408115000c1a1071b0781c0407001d02108030300142a44066814a98074000d160500b0322514480c040c6103444081c1c40f0100a81102800b070300000104000c0b02c14041171710840c2000510400004000e00801c10081046103200040c1179042c1c00c0000c0414080d0b082034040f07a0f000b400005214142666100480e8824405c1e18140079040c0103900110309a8410745210f203904 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 837791034 1250 837789784 837789791
    0x1030209060f0a060309140102070c051203071a0403050d0c050307030e19030c08120108030a11030a020d030b1801170f07120227070c0c06090812130b030109 69
    0x46005115480350300601803405154901c42c82c0740e0782d488071910b10f001c032445403400003604031840c0f0300280c09840e03449616045600205044c0140030a1002c00c10840d0401c482c40c2c1648445124107603128000d05402411030003186080395039038600c802d940f83d0312038801d191807882c06614070174031022209002d1b580d20000b00c0110400c000150144103070340f40394416900034174031280d10201e03803500f44800800c010204a901084041000020804c1c0d40070301140d5550024190303121400c080c0c0e04d800030b0703000c280001c20078802a042000044101e0720f2813401980500344040940d041940130700314580990740c102040306220420042401500c0703018140c04d40c4001058011000340f24905901d0040810960b0461001004850541100f050700246d041d2100300d0766000301c409001c07078080e42405980d58100e6003c02c00400396480340002400c0b40c420000d20651a48841c0200e94900c194011a410390f0322081549c401030102c0e0b009441b00d040b040d80401d89a030745503c2c1c0501140c0080e4440b0006648 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 837792284 1250 837791034 837791039
    0x100507140610060509060301050d030e1203071703070804020f031c120c080c041205011d030901021e03070f050705100f090503060709030227150918032b060603020301 73
    0x540b40030000401d00da10302039042006081c0001d102d40b01c18070885208440364005d440030540103803040506260700404103c48030401c42412500c1c0c0d07203c0101120a003072840300352030300000c0345020b49009940759940d10100d9941e55083c001d106041c1c060860381841410048818850b815800c0c2c2c40504a550b02c2c813000d915400300010a4412014aa00a00c1141020001200c05034402c1e0703404c880e1100070304400e030012410300c240100708100e640b100420320707403041c10341595000000b41156a000c0e82200d1003110310316400c0008291120f21008160404c005a0340860001c201c0401c8881c041c40c01e136010a50307140e0024141c9041b02c0840800705041c031501940d640d4020b60104020305055014000701d00c0d06203001031441e00e05000003481040c0201c1c020382006085480041201c5044460b841c05081120784411006028065a44100b050320700040e07a000c1000070070380c1c1400012004500b8101c0c82100e01800c0035442030000d4400a4003170f0f985015079030301e02034040100810780f80140d9a50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 837793534 1250 837792284 837792301
    0x10b1809180601091413080f252a080d0f09090e1f0b090c220e0a0608032814120415020304231203011401020c1507021005071406 57
    0x5c8000304a103800c1c00f4600e00c0380022a10714011a4450400c00503500da85507d60051118078051012017500b64901c1d01845200304070045c0d039909010401100505828010a805030124090302c1c002c5804a40180462050b664001c14110225503101c2c1041ca40b110b8030748581e0012030780a07000c03000c81644015440c8640100e007a860000c00703502950140448240d21020440a46010300fa00000010002c0c05c202100b42c155a8000409a1800604041651040b4044010005a0b0700200d014a0440006034560001007108c1c44800038266909840c83d01400b035152229842000c04140403034101e036915610540c40003010030807010f91030307100c0c1424281007030400000c610800f251960f10410070310010130844240f0b040d8100035107030000c0004914504803414100483c1000401010100000c00c44418040c910001604207a003210072803040c503c04c2046040550500c3d030102d50003007000c14058100003e814074800c1c200c2c1816894148a80c4e5120100848103040000c41d4129506005124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 837794784 1250 837793534 837793571
    0x30609020726090303121605130b0f040e07030c0908070e0f130512030a15140d050c040903020a05010e0d09091814031206010206060112200a05070605010b180918060109 74
    0x51f00e4903d0704506000d01106d020203140036034056040d2034030300410101c0c490803460040300c024109182c20b110450030808809800340c0100604803002c0b985a03500031980c0000058500e00300e81103007101600545910740070303c0250001801408508116100c01c001042c420081c0c1803d180300c840280b40d03240381161221007251220f447c15000a1580602040f10780b6007440d1085100d80100c540d88181c007507510700702d80317480070550016070481c1c20004518180754001c2000240701d4012002481480031552003503441e1080c50201d0004640b05507002d01003100d240c1d100c0b1040c2040b44040e55100525a00d981c0650134140c2005e0840d94400100e85420345c40d0890310580000080c00188402d00b081c10000c0d010b151003c3d40d2400c80d0750b83d1130800c00042c200c0d4440020720074040400c1c540c1e403905c2d0300e00100342c2c0d841014290b0b803079400d100002a00d10100381c00c1341e42d10092a210f9414500f0302d0402c00c42044405441203070606040030810101c01e000380040342c020240c826000900d00f0307a807040d01002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 837796034 1250 837794784 837794821
    0xf070515041a0d1b050d1a040e160f05030d050706060915032306061c15051608041a07020109061a010207140a060c08070807060c03060902072609030312 67
    0x10313040e101400150180c00800765030201ca800a00030071484402004035501e4005010039680c802e00b4907400302e18114011071040100142030f40340c0341d941c9860b030360800e002c0500c80c458142c01d80e20401d001c3c402d60f8402c001406001d40315420102c2d0681c2c0c0c901f4100140d8000b0003015480d044000c00410410054400c00c842c4445402003c0e0b601210b82c00e07801b40c894900404081c0104440f03603010b55403410280720072030401d42c840d070740d10841c0c0c07458454500103103000c03a0800c00a45041c0e82082d03c0d17902821903180304590080d003007081c460070b004d03120702840c201624010542d034a420001000840d02e000340001183c24900407804002e070040020b150000c0343e0b000e01101e03070f01e003080302021752103009400c1e06907001400d05002c41c0c0107625110180e840384040c00740c01148003042c004200001a00504c44401c4c00e65401d00c0b40039141c01c0c2000403071203244402040ca4445903012150a07140f01d800e4041c0c19107803ea01401c1210183c04203096510445003489034042c69002c01c58940340000c40b8494 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 837797284 1250 837796034 837796061
    0x10030b010b090a120515060a09050f0702151317090d060b09010902070b040b060604031a010509010b09061206040608030406120f0506030a0b040809100216080f070515041a0d 76
    0x1310845c1e110030707413030384200351603600c24200300400194940c68908100000f0440e09200b0405032030000308a8a038244140c1e48400107004010304410540c40038071100c4e009200d19004e4264048180d60f5200e42d00284445521051200f401070002964074100000b680e18050200418065203140800000100580160900510500401000c00c09150078558000e80c8141000705070346401001880354001da50004200c4c84070300841c44440f245044000d0b04a5205843c900d0199803500c4800352980030307036400190000c0e003d01410891041003c0a241c0006003d400001c58075281d134207060441e4000e030891000305040820110300d01e03c842c03044032080005048104660b00708240003a403a10000b0310301400030024400454140510030f401c98007942c400070140784040746104806500c030b400d40034014140c0a00361100085281006c956034485407229005403044906007020040d04406c0504c0e01c132140601444003041180310141e81c120040246903016841d101e584a06605542403000f4416 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 837798534 1250 837797284 837797309
    0x10318120801212003190506151e010e0a09150803210a0b1903051b0a05041508010213260307060c0c050109081b0a050a0b10030b010b090a 61
    0x5103d181c044400402540c0c07100703080c0701d00c000400103c0034940c0b0002c6080e034140aa17502005100704c1d2030360310b05405842a03003601d060b5035414140d5100041c3c0c841ba480c0c0c1100c2d484d80d00504032440307418560a440e005041c072150105080b00450790544e00ca070040078207949d40f01c0c03e00b491b003106d5210400003007a941000390329020701268400030000003c0c0208450040034408a01000c00d190441c03140a4406020b2080b4a01401800c1c646800688015160381c0a84401410003200381c000d950880e4201814040d812071500d02444001c0c0880000b0709200c48103440d000c1420007080c00140141c81c042c0401500301030a24170104c0b0081d80480e41442c0b1206407000c640100e481c040b081e203141982040c00081c040a038080c05403030f0100800e800400f554a480c03410800c22070302d0405080741c260540700d500c801c00000c6a81655595004c01702502070313845140000d000a0074100450340c07020203400100036007940c980d181a4280c1d001e8000300c2040e540811003440d40d080c0084800010405a00080d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 837799784 1250 837798534 837798569
    0x30f0509032d0c03070210030b01081602010603020310050105090f04120509150a0c0506011208040311030a0209090d2d0e030304050303070606030b06060f031302010318120801 77
    0x19600d208418928640c0e9810707000480a8070b0003001c0341400c406601d00440d5591403010905a26980250002c92182075042c0b404500c85120780f060b00d500b018107031038040306600ca031300e00c07981001c4400300c001d4215900d8000100050300c042c04100c08000ca1010003180c954100720400624010040c20350312a0440c500030000400d1854104032044c805508019540340607001c040781440e5900d507500640540001110075100750702c00d6414a28a00031401c0d1012643c9546c403102040900f6100901400c80c04d02080c40490051000100310f0034000f000c5550701c1e54290b0100c2d00c5540d0895910480e50400003407032031001c4d0072080e02541c8030f00e914805800c0c079000218003031014079814815002c03c00c0d080c8690f400c0741c6040040b100500710080449071500e0403840c084010300b4803400f08a46008824000c1003c0b81014401d94032202160000c4a0a59890074024a945d01d0104000d0f410141c03900c040c0b00c045a9074007484103c550080701000700d221f00b40c0d01d025010316010784c00b1000507007078074544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 837801034 1250 837799784 837799801
    0x3020910080405030f071a070804060b04020406140310170303150306240307081b040f0615050a031113061d010905060705070b0d0c120506031b0414040302010b01030f05 74
    0x201d030340407182030340410341b80c44850a1003210125a0301c88945101035071002d0003012500402164030591045505010140401302444240c0c080c0c1c0c4182c9003c501000031a50041c804034010b140e12600e0002c0c1010029038880c200c0420091908002c4110b4000000380f025510100f000203102480c160010102e038101408094180d5103070b0340000040701c0c1541d42c04030455400b4003039140100780c00c004448085824410104100081c01d040034455898088407181144a60041100310340150740602f0b1160b00344e08064a07580d00031041102059a10444c103840c0700c100901410125a8000389103114506142c00600b9025540d2812410914038041d58034882e03030300145200c252201550720940300c10352880d050740b8043e416000080c14180c00b00b03c11520140750340c001c901114507a5101041140f80038103034422603c00791440c58041d0071403082c00001054444d0800d90800c4080c100088854078088105c035104000c0c0c4045005135162245034000c1c0d030340360060304200c0c06503440801490501289 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 837802284 1250 837801034 837801037
    0x60e010b041805150d061a012f0f0a030903021c020a03080d0209041b090512150403050c0f0c010e060a0503061c170a02060703020f1b0313060302091008040503 70
    0x100180940c0c83d40c0c0007441581407025403074488000901300c014001c196292900140c24034801500000c080c10318008180e40c07054209a039402400031040c1407200c50030555a40c11070302507844210910035441d20701c0c0e1446082010403c402c1c00781d81c40aaa042c2140304003c0c8000180c084d000d0108501440f4034090303942c0e000103034216a80455400d80c1e51210031280c101a000781c1c400c040e40301d841c03c0e580c010400d400018003c1401190b03601c0c0d0407a59211010417004c1944c080e010a140d610120540e5199001e1a1038030390414004d00780300d8280071a1019645c9000d4100c0103291854003c0c104065145d40c022014410b0510704541c00c1e400c01420010062a030b020040050b4400d0142e41380300a0707021843e9205000342030b007099000b0101d0a006a54100c03503801011260010b10591000451042c0300340300b951030494400700b1146c03826a5000342941c4030003690020241d580000c11140ca0030a503030003101d83c020b14881d00c02503222000d800c204251065501c20030014070500c0350030040060004030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 837803534 1250 837802284 837802319
    0xd0221031909060504031505062409101e0f020a080414030d0504050d080906070c2603070c2d060306080f06070512040606180b091305060a020706020c01020409060e010b04 75
    0x44005140d58565002805008170289022b0803040318a1143d51f01c0e0b80c44074010681c0820aa4400c4070341074800a0072101456401a2000518440540c602046200d8420034043c1e40ba0b9204540321030107207446056841d8800e034800c84141c4980d43c08400682000c1c07004419680442c01c2490a00349800c0214101408604c40184150300001e11061140d99440076602801c0c3c00004281c201601c401c50754802849111644028501000341070755005000001c541300190310044a400303540c9013419081fa0148000e400100812030031800e101501e400c0030448009000d41e0b6004900c0f140303808041414601a0040700317904d4ec000e03034204403500b9041b078215016041c0910074650141e4807814488010041c541101f0320103003004400040007803031a0800e1300141c5003110368445035100c03146880d0341990302001c010642d82180d000204140e410354080d04000340262009440c01034910f4030b4608a07401900210145a501c9800303200300380d09094080c0c050318a040307a4518207818500451500182c12 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 837804784 1250 837803534 837803573
    0xa0602030f0903070f061112030907050111030909070306061b080901050901110111040303170f04030509031009081e030c0301270c080109050c07020d022103190906050403 75
    0x10b01495640c0301000004010301d5074007040c50450391120001009030301590386107803141c81800d618840c01d036162000c0f24002c401200041a03440d140030b00640e44050102807000c5d403800180180d400703584500d411184250341c19079000418500b0090060414805400180f10801020703c03c1c0000171090801c13180e807a05c0900300182c0312100000103d41d407903031680101c000b81d424881081c050303012000280040d24442d407074050303854404051601ca413030000c07030721092507000c0100403401007401070004102c486400340030344051070b100701d401e1000d46141e070750b089400d03540009000c40f140d20000daa5448048072058800d1a5041c9803403503c56a000601a941c140c0720550504040040b041240c03503512110240203100e0300a4025014003842001d10174010b1090400d0002100344040c0800c60318a03a0307000340048064031080e000d00184020181090300c01b40e10482c90307012407900420160002820344402000c0245e84942c00401d0030380103078400814020140014000030f0650019020100c120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 837806034 1250 837804784 837804787
    0x60801023c04090e120f0a081f0f0e0c0a020715030f06060c03090504020910050f0c0f060403020706090e06040c03110c0a0b06030d050f130b0f0a0305060a0602030f 72
    0x241400200c91114282600141c8900042c001555000307a04281003070840942581c0c0d1035110b10409030030611401ca00c1e1080b010b02003011074850740c00b07070100b02d8004040503101210590200450741d1070840a801c03440301140701d03003010060300e458403c03020703403010301404030750b0400d02ca070300000e55541c0840c0184030240508942103154a4402c3e80a4904414246002c0c016240d0311400580502c0e4000000c0c0c0c00503030000c07404111800c0034000c0f109201c401400322194200307021012540b5800504581c000700004000901412008020480f40c01031404003500c00b900742031030702900d00b04031030f4801c0083c0f02071000308101c3c4a489081440e400302060310b0128141900c0d1000310020012002000020f42e804250180e14640008001c06510310035000318030300c0d803501003c0603940c036642034200b000500200300c0d0400020703c44025000c14451581f00c1d840b40c5440d400b040d4925001403040180c201d0b80826141c001340e41c5801000d4020a05813039030405c0c1e84c10640025103d01c681c2940d80d081960 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 837807284 1250 837806034 837806107
    0x911060304050c04140f090601030308010b070309050618120115090c030f0c02070501020f01021602150f040e060915010c11011709010e0705030f100b040204030b130606080102 77
    0xc0c02140c4403c00003c10820114000903910280414191051441000700c003000691144000496a05803505511420100c0e8a4016a52460381c04803208508010b8090310024061f1079480107010111000080b1246030700304d040074480382c04415031400e9441d07030520319865081c4c035512860b00c0980f01c0850010035203200748103040c5c2c0039081d88500c6d1303071585140c012000030440d400300d18030058507005da090b00c1582d078040540074240d016043e4016004200741483d000186461002c06070400e07440c06019007480c0111650040c1b5400c1076001d41450700c0010708020207458410401c0c2d6200e00070740810002e0307140c413200080100c0d4820394024000e039003d4031104190b03030281e443c6482445084524070004d10f41842928081c0c203400700e8800c01c42c4030b0b000002c202880c000c1009821407448500606600c024140104007410f40324801c070740c01540c20070021010802d4919203034880d2107400c5845c02001210b1404c0707001c4402c0e60b840f0614503413060100920891030740c0a204050307203001070044c14592 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 837808534 1250 837807284 837807293
    0x9090f0204080f010614030a03020615010c12080a0c1403070809100c03091202071a03070318030314070e06160c0b21070e0d0b07030902120c130911060304 68
    0x4510742180da042d00c02d07010380303da480e10150000030a8903103405840400548000a25070758461181c0018007581000d00004c4164540c400350180440d0145058640800c0b0740e00d5080603198522a039100140c4c6d243c0801654030004c2c0548018004c0e10310342100e04400035a11368049000181c004010420b030040480c0940030100421192079511500400009800b408041d000b811051400c0f1185816049407040845c0080f400d84d01302c0f000300941e05002c6a00107181d1102e0b500050140061541d12400d645000700a42c00c445c0105100341c5001508217540003011706020001424481040703041c902c0c42c41d50f9140c3c4420760790301c0c3c0b40f50950f52146414a1070310820341441034026240c002c0000c5900c106021245001e00242c032110100205542c803003140456140f5440781507150404501d0141e00001303000340c062a503214000b07190005060300198001040c030000780c0f250007115808080a41140c3c90444611410301100320000c00c07460000e95104012107280710380d201d04c41c18001c0002004d01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 837809784 1250 837808534 837808537
    0x8120603011b050d06080c06070f030201180f350c07030203060f010e01090b0f0d141615111902060d090506070e010f1e0509061201090b0a0609090f02 66
    0x7241e001c8101c0340c1920524002e01c02e4025924138924142403080c00a09200049040c10828002a00d41840c0030b0641d250703912108008a0f0482c1190740e50b11541c0300203015401070110ba54403d249488608210303003000740c581c2c0d52a2203001c6d100001c84141014401d6400e41c00e48402c43c3d08108107485a000e145078504201c241d500194044c040e40302085800c00e5005440c50681e006c1400c0300307071640d0301c500410040b900035108054004100ea0420402864000f0303004905c60b21898443d010320b00740b400c0c003c0c280b20030b24050150044207101e0610070b0040c0b00788400b4070310300d4603d01001d00000d1007880c00c4d0b85d01c50004a01a11481e0880e0107000c0d0f403100e104890b8a241400018000600345140043e541c480484c1c0d11400070304940c224682c0c5610924038413035041c0050303695452804d2516031046007464081c00210600c0f90420009005450b281d01a2004559004a400c40d640c5003031040000d50701e01d820858800c2c0e119100c144040d87c1c01080d00c005076403100b4400600740301c844420714001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 837811034 1250 837809784 837809801
    0x60307140315090706031404333b060109110f031005180c030f0a06080f03030a11071211010609060b130e160e0d1211070b070812060301 60
    0xa40c2d40400410801c500b00140b044100c41c0140d4080107141d124548020007a030081d034004003400240740a0b042e001e8005200c00000d0500c82d0a17070340c00d00e145d0040a0341200d10000100d54040d03098204d401e011a01d1580c2d0f00824103400c200080c2008a91070f0700c9032207180501529110700d40e90140c100382514503070141e41c015603100304055507e04002c0121840780c510f42c801d00c2d1144d06134034807510080d8481c4250f1801078658400c11070850315078402c02a0254001001c641c10283e66030310004561500b00300c00c1c1000b050b0399000e541e581c10461414001c0e80d9000d03403c06800c01081000b03d0000300400f80d0342c0c9011400d417400072407a440e1142203d001d0318150340050085810f2036000701d6580b81e01d80041c43c410012817000400703990354005511110004481e9420349488085244c1121801903c00d40c85690000f0030b20301c1b00310101d0b50b88400416100d82d070b01c0001032200501c051190810402c80004d82002da10031410a0301554038104184210380002440d500342c000882e03000d84094201109 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 837812284 1250 837811034 837811063
    0xa080c040e0102070f052a15090d17041a03070e011d090406020d0f05040c0b070510020f191b11060d0e0606010e0117060f18070302040306140603071403 67
    0x1c5d013142609007690394215a00710550000d20600d01031040c0740c144809100903d001822603007002400545000190b00007140302c82e00a041550000e0015000021822280e0000805c881c6c46034182002400503080305805200aa1010400d00c1f0005800c0010040e8000091810540503002c2542004403480c0c143c40b699005100e0106000c1041840c1e0041d1580b1a40403500b007041c600c41e0900241510810b5401405c1e0400c0382406120303001644004001c00d902070005c9030062030000c840e81e012a40304c000c5c00c420303e01d00072625040c0000456002c4d180c03201a4a004810030448171002c1e50800c0007074000401154130071407104280d03191002590740400c1c4082c8200445480c81e1030054032218101c600c5400103181581555186d03000340088006440b11824100351603035003005000f21010010f04160b03020000304601c0c11084401418030340302e0302d0b1a68015859601c1d5150001c00d603203613000e100192801c10381c2004881d80700020028200c2c3c02003090108080b0846001c41d0901c40e0b219001d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 837813534 1250 837812284 837812303
    0x5061c091401020f1b01090201171e100e07020a1109070905091303031d120309030423030c090f0f041e0309240518030721060b0a080c040e010207 64
    0x482410b00020303182c45c8144240c1e0442140e40c0c60034984c01c0b81d683c2003009000c14601e0403140c51110050004951160b0b5404882680d480000354508400c00c0c02c907440040c1c407100320070500c000f0012080c00e079000003040c0014034940000c0c2d514102c1c024200700c0c3c02d501802e14600042d417000e03c101c10a5004001c080c08d0242c2e507003000703540c80c800c5c0c0c800403000740d000c241418500503402c00c00d54281090a4002e202419910780c5542d0600c0d00c1d5070000e040004544010f2201149a014420240701605014010709014031002401c1c1401c1c860080e0616101c2c41888007001146100c0702c05040d44003c110103104c0349959a40703011045c41980308a01882c44076243d0a1004042c0c0069211098420f190752040500d400081240404c0c0c1a41c0c03041c0d00000c070b0501100498010f01e01404812000050584d242c0649504a041610001511307001da030401250380b4000384403c511401c16031140565001c0003007810800016a02d94500f907403103000d80e036544c52001030b01400394181c541c425030058101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 837814784 1250 837813534 837813547
    0x1050907050d020d050c0306030105062d0d021504060206010e060109060f09030b1906080a08090d03050c011b0e0d170703030f05040b07020f0a050d2f030a0905061c09140102 76
    0x700c454004442c100d00035031030400802c00e20302e0980386e1812070345247ca841c4042e600d440e40c204102002200303c0c55422413ba107000c40010781c3d40c0303c0c2652002000e0390010b074886243c4500240fa00f00c0c103074402c941c640c0841d402e0004c00d903400402c00058800342e06140703035030b8202030f00222001c0a46a1001d840c640f480d8007072102d40e07808030a0303908000b03000c020b003401017a0b111144c060700c80c80c442e41300502d054010806030359103040540c0b049090b0340c00303400c0550802ca5030950280c00d660b1107020101114110880c2c9420300d68109050100008003036813042108a000d5456840e500c40c1000c0044103c0d0740030800604152098021804079011000305200341d00b080d10307084161482c155030303002c0540550342003101c1c3c01000095001d89c1c42c0e0004020040c141140f00166031032514450b455280c00c00d04035403a15219022040580d020b4880c400540d41d801804000800c02c0740c2d13070741081c0d2003024100902084803150707050368140d50000e0701c40050446050310309182246245845a0b11790750010a55 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 837816034 1250 837814784 837814801
    0x7060914010e100e060112060c020a08030709031a0f01030602030c040b0708030906130b0f072d080601030e100e011509060303031104080318060408070305070f0e01050907050d020d05 80
    0x1143c0e009108607403e02ca000c00707042c00d80751610405d0240100800181ca420300c0429241c1e08940790594050042c1c4d030307400b80191030f40301841e4400c44011001c0707856120100100320385081c00055441200600303044504000c42c019082110600c4080c000c686c001c0007142e0303840c0d451001c4400070b01c008a000c1e940c4000d207103802c4285800490794944c0b1401000c00240780c0050150448001b0b179441040380000c4c1e580c0c43d0200e1a801c60280c5490100507110030940590841048181c0e0780c010295580005103052540041c1040341c000d2403641094240340f4403c51005002446040e0100380700d0f40800c22110341c203400c500400014242c5c04400307944580024135a1a15480002628041c0c0c2c1c05110405401030010074522451140c903c1640c020060f0090783c4030791680380c0c0746607000204154501961950000c2c03038110107802c06e50303c0741c0014a00b048044664207031903000300824509824258501030000f8200700d002803a400c203110340041d05410910603603040310608c6510000030011030809800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 837817284 1250 837816034 837816043
    0xe070801090c08010203040f12020106030606090e0705010e0d110d0b040309080111040f06080a0f0c110f07050a18090c0f0302010201140910150f0b03071e0507060914010e 75
    0x1000c1d00c00d0750b01d1400214141c4418000c0342e00c1590014111140d013015541d80100d4020200501400c5540e00c5d0404000240d0a010b04001024200f0001c5211030030010450705055166000506022881441811a403210308507485030980180820060351221404507003806000d10000b88061500000c010403d0380100c901019554000020402000e00c81030f644100e1140780140c100c2e104c0360310010440b0303520a040c1c0982c4440040c6000c25451900c2c080c800c2a100201316000c0030880416000c3c1201004108003161011154024580c892030200441c000c403e0b1030048403954000700c0f03c080352141c11908820b040d1688580c2d094170a42c0c0d0742c900c4c0804000345000c200d00550030000842080c0040310708003401203941001400244c85e11181340c0740104044154000d010401c40c03800103061041c00704000050400300202956031410b143c00030700c4034000c07041e4040c0e1a41d010302082e615940c001c055504180c0c1c003840004081c28079060030390f00c030709444242c8080d56007480000342c1c10a00c0810b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 837818534 1250 837817284 837817301
    0x150b0d0501030b01081f18140718060e010e04051609050610020607080114030705060c011505060a09210b04150e070e130311160e1308090111010e070801 67
    0x25007504590b01c494016440701a46104c041c0c00164078405191200100e0748240e24802c0c46416261213100f2a68230098081400412404560040380c0c0c104144964030741d8441011144441c2086003508000c40300f101c446041c002c1d0703081e40300300b64002020040208164030782400a140e0192800da55006504041c0c6412aa0700c2d000c1e030b800e01581170a40d0b0002581c140038a030b003915110032aa00300100240b42c100580e200c56418070900c0000919034964100820034040814008211030811150700f40304025150f11a0340180030811100c0401a8048407036000c1c1e13542209144020041100300d520342ca59150070107401c600e07884090000b00603803004681001104042c06011544c48003103015154072203481181804000b80c40001d0416103505003502d040e034031038140540000c080c01680c034030301000101c8200354400b08160034000080c0c1d62030704540c8400c082255542200d86552940704078007440f412141804040d1541d031140b20406c3d0480c030b54465000701250803407551a00118041c00d20070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 837819784 1250 837818534 837818543
    0xf0f070f0b0406090c0605090d060e1c110606031f20040e07020f0624120102040f0906090606050f0c1f1e0e120c01020906070602120a0c0909150b0d050103 68
    0x200000d81e1b103000700160f81c444100205566500b0200351a03443c013502950018511600410011640891704034a4a214500655648803100b20b203001901e441c094024280521070b03409020b480d243c3c8840520344101c4266161000706142e030703c034103580314040d00b00d1044491042003c540494003502170340f44c2d148074118660807190313400c41000d0038070f0f2a0031301543d00b17903441c606024240c00d0080c0002d0004c3d0a2440c09003002032448182c1c210705003260419082580418160401040b0b5100c5900911003e020307280c0b801c101283c41e248002e0400c1c8500d100a00b175196011a8000c50f840050080d038203003902d80006a40f06d8010550002e0040400104142ca41001c650380c5d6a0030800b1403290032001500c403030040900c41035404501c0940c0d0040e002008066401b0480d03500701d92601006080c00600c03e40c400342c1c03a803c00700e20f030700d000c40001403000d408140b41070710303e4204941c000c041030308580740e0090016404200c0011807280720031a80206070074a10000c0c104448810a030300c600c0c100c9005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 837821034 1250 837819784 837819803
    0x60102010b0a05030c010c24050403080f011512150b1b0309100305090307052d03030621030403050106180b0108070203120604060510090611030f0f070f0b040609 71
    0x24010041004120f019440e050f40c000c10580c1e00b5035000d0078420504a0168140400380c0002d446085005110400b0710581d143d10380050008064020b01e66030341112061200a800e1342c1414002c0c100140d002c0c03210b2081100700121444000c0b0f081e40003d20001c00083d03801102d035125000c14041d0341c006404c1051492003a980002c40c484080160b0700e50440042c4613152101c4001000c034054400500114020b0108103c5940060380403c00c4051560107a40002e0182c09828180083c00703c0c00708417400560001c01c1000215aa024503000800c17160765413466590000a90107442d500840d08001d10540c40c0140100d400000040349171034000d000d032000d0240200d000e00444194000f0f90b01e540250f4000d02c00000b400c3c4c0c24540c075661090002d0320002e021644c51000680302c40d040c44d500c6022860300542400016032000d004144c2d421407038010342c905152001141c00911441503a1540300d9404590442040107000550441079088507850f03016080c54208403000305224002103600004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 837822284 1250 837821034 837821051
    0x40e0f0f150643020f04020306011107151d10080702010f022d070c030b0903090406032a0b04030b151012230a09030e1e030c06190f05070c0b0306010201 67
    0x1c1c543e946015800b0b4a0059112101c005202c007070340000e80302c10305000640e1064102e50800b000700c0c10007450034124003101108800c5026001c056000042c03500e0700017500310310503180c40740c1e003007600c5103031320b6151413080c5a40d881c40490040080b030b20090155400080c03801e80326007045400c1e0851402d0401c244074051084d0909004034403030f12600511040c9124410404246120744159110303540d070f82a0783c0340c50300d0300000508641054000711920b00044a162078250180b00080e4030741d1001100500d6510b0410724020428080c9200007401d01800300f001a040c6a036403441440f80303030009800603240502c6001c01404941010514642e0345203080700d0040b03034074405100f541d940200b450341c19066460351803e080150800c403109030244039285410b003200d621364440411740760f10700c0340c1038401c000f07090380826051801e000841c500c1a032040c800781c0785803251101650070f80419401c044103e40c11951080c1c034180070b080c9002c1c1001420010014940d074511005512030300c0300341c2c0200840d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 837823534 1250 837822284 837822397
    0x6150f091005150403020d0c210c1a121618150c050a02090c180603010e06040b0a0f06050406080a0c14030c09040908040e0f0f1506 58
    0x40c0d085410286000714180308000509103440d1440014000c1c410561400d0f40301d40200741011820041265407070403190b001c001d1003003c0c54a41c140c1046242070152061400c0d15100b400c5502ea01610113000f0782100c030b5580d0075060800321240400c0c0c030540d280c42c0c0c1c900311119401281c1128940004204107006402003030010318480c0d82580d004070001050212400000c441c0a02032000031074192090390310b05005643e1300c403d4284196a810041d42c0d441141c030301c11602100660b15414001c2c1400d1006000c0140000c03000e561101c7d00b91070000383c04003000d000841c40705559110302050a0500004105d89074864020000e65038282c45012981d00d44015040c1243c5c18103e088000031030340c01460307034206a058000c541000800b452142024200c90000f011101101c00c100c0b10b10700c2c0020308106032522061440d074410000181610a0300e4a20f41540b00280011b01a103d02c040703801200c1e109580b400141c0300b00724180d03800502050b0b071481000103000b520083d4000440c84144583c2c6030745 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 837824784 1250 837823534 837823549
    0xf01140102160b0a1202180a151218020d0f021c0f021201020405100518012d1209050a1703190b030c1903030e091308031806150f 57
    0x81c50b24860400e6010724001ca0000b0f5074000c40640001c000326000592801429070001c0c28410050000990103813110304100201101985d01c2211a8022030140180d00c58000c90880490f031001e4a0109142a1890080c4019441d00f00000d43c041c08282c40034080c0f000342c0c0039440314240300780d038208200159003140303001100030400c0007045103161028403401403e105882c2644442c51200160401b038482000a84498400004000040d004581c07450503603d4411404c5400c5020300300f1a1108280101c0940704040700200b50182c155071002d401032291081038806140703403081108008040040c40e0640d00c031460a0002d0b500d0016041d2450600070382081103034015a10002102e03801c44415201c10090160f03181e01d03550601610f000c00341c0a4440307000e44d440350ba10246004082d01d040d460003400c1d142050f603885015035003003020400000b10300f0480c03004036500b1514460b1665200c03102d41c1e08142140d03085c41d8003130180f442446030f00c0d00c209104131195002156015201060b40c014001103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 837826034 1250 837824784 837824803
    0xe0a03020a031211060c0d0e0a021f12061a1e03131b081f1808031e04030c030302070525081203040809220212070809010b0f04021305090f01140102 65
    0x11b00000300020190148541d00040013040d4a00658400040035000205841c46c402c210007820141c00414008a55004101c055202800c0c0c000300300c1c260034003050f03076410710550461821582c0005150120f000020015400040042030029540d107440150b070310011600c00300c120b4a24072015038104503000f0300d1020740c0548400310010414001c10601c105010b401204290035050f0b034444400c00c0a4400c140403c01d100c0c001e4483d00e03030f2410054400c502411201c001088108040000e01c000a035020710010506a054600561282081d05110341011f041c41108480d01d403003210189601c000d035a0f18041291054010b494681000d664219100d01c012540100a0a4100072041c0305281040d220865451038010441d1511031090721030f0200d80c0026010070100d001c0c2d0741081202980503d440f03030301c00c00080080c0040100000801c01440072001c45a100ea07401060640352500e401c0e00500003880000c140103e03034103020055400103882070040c5451156854019a800d5000040002c3c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 837827284 1250 837826034 837826051
    0xe040b03060408090414011e06021c20010c03060305010608010207230102091002010b030c010e100f030b04020a0302071506050604270e06070207091b0e0a03020a03121106 75
    0x141d0b03a281e64440c0c00c40e0f44038031001644155175541120303042141da0185400380c4003500750340d411003031110104d40f01d682090744201e0855001c0031781410079401c0182d8400d00b010440c2044c000e403803c07140503407001003a86602032640358601181d0b011161350580060080b24000d000811515450f48211400d034412150080c1240075145031982d1700c1d0250300160102c0041c000d00060400f03656070300186c2403400d509035980060b0346a0100420750314040c00a003122007000d080100d251501807001c94440780c0e2880c1c2c1c5030180b204804024003400e00940200d0100e0300020021542c9183c079420250007500140030980f13881c0501c1c0c1c030030074a190a92180c0c0090310001030126040074178100c0c1d01d1b4013406010380200c442d040590959401c44641d8080ca68010703c51a0180c5502d103004c660003440d00d0810751081115500b45001382508a41401042c0b62861071842e201606650ba540800d018600b2644000d402803251540002846552101c8188401559440a4204202454441d902d103000d550404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 837828534 1250 837827284 837827293
    0x18010203060307260607081909021f0201090c080706090e0705091e0904060603060b0121150302060f2a0303011202130c051902031206061b1c0e040b03 66
    0x82c4d4441ca40030314000344d0341c0d00104440c10080198080c20301d40d084e111107010a00c110306110703600c84d40306d0800c40c1130710703012404100514068000610040f2414000c2d0740303803021201030003c2103200790005580c168004c0301c0406078070341d00c00149990b1503951113810b00250380d540300851010080001580504095990340381450361010400040d00e88807071120300c1c40030a0f401044000d40322080014819406188005602465030900b0400d680450307c0460403c0200318040400692036031503400d01c01c905060001c0c10a800c65a6495201070300e0300040c4d0301903000315920340340010100040003280c1e85c4001c2c1c0c1c0300a4201c030300e002904141d28a801c1000d50018401030200345003802e1a0403845000030030600105402e509813904583d40c0d0f07500f44000440c0001d5040202c611402010000200c1e403004500e407507810582c044151001402c041d1013000001658ad41c00c4c0303040300d001c2c2d511508140a40d03200d180c07224003503c03003116442c26480200342200a4030b0780d2407130503115001d074045000c1c0141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 837829784 1250 837828534 837828539
    0x30f070311121009030e01080f041a060f0d0b04060b0607050303040b1b0a020601030c12050a060902030c030607080f0601080106050a080901020f071113020a0c150f110318010203060307 81
    0x1d94000d8910000d0303100c3c40344286074210070038103006100c1e1080c040e4803800412280d00d40010261fa1000702684160301046003031100188400341056680e1900c0c400c03203059500c503c00001c08070400a00324940c024545460380701030000025016026600c6a501004800d0030041408018082c055020381190010320008010070552600c5951003982811201140721000c2c01068007074004e031003035800503071240c5c005200701b00c2c268001c10090100301c09174040c5000c55035105a0b440a40c4440201040c2c1c46000071811520100004521001c0c003e040d03909500d000040101026001c440600300700340c0e8100072819950140030400d05030b803065901e0602c1c100f5001c006441028002d00801615076081024074000044400a4040c1c9880f401250a4200c5907504101c1411b0f14540b103007803030a01c1002009041d68014550004159124080301c07521346140c840240246004050b00c004242040e40485d0703001e062100440c0302d51043d00f0f00600c520080034110b405c0b400200c5a042e0142c0c4a030005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 837831034 1250 837829784 837829789
    0x609011a0306030718090b0a200c12041205010f050402090420091f08032b0f02040e250806060c010207060c0206040212190f1b0b09030f070311 63
    0x259403041c00070f0125410b0682c0e0782451050310200c2d005807000140d40e04030300010850000d0707507590008881203060020440b00b681802d6407000350100c42c43d003140005100c000c07021040c046850b200c1802c502d070944481d0784202c1d2059105412a04070b4255191003002d000e1800c0b60311805006035006000850302e503840d6a1400020842089020400368400010841a6603031261041c0708211540c901d540300146002a480030751300b19048036044c1c0d002444003e82818100790b05040e07a4070340c4220b1903100f8071581142001000211091036483d4000030300410030f00901924503001e081d81c0d458000e203031801d000e490038401450503d00c00001c0c103c2c101149c064540000500044465400010304d00a51940c1d000112440d0b00c06c0c2901607080f803400c04c015441e090b0502d010b088030340c901a0a20060415070308014120450008040b0f8200200920038041400b00114108000c2d501030324040e62104110540c03500500c1c0418800c4c8110f4440c04100c2d240400e64100300c0754066681c100907000c2e00308 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 837832284 1250 837831034 837831037
    0x3030c020f01120c0f02120f0304171303080304110916231605060c040b030c0a03060806040b01051306061e05070203150109140f040615090c03140609011a 68
    0x100b410030900c01040084401184241e400980e40303038031900000d5001210181c00e200c81030213000710307032101400f111203d19440b0040300d41c09540400403070030300080320040c0b00703860142e00304c0d0b6200300c0925200030040100c408001d5001d43e0150041c1086050640204041444100e036403805001c20b052503108c006d80600c0099950f41d0028514142903101141140c455400c0441c805045d00a000b401c0824040d05018240d0003000028010746007600304a481412448040d00c0410080000218602028031a61003403028209201c20389060f07081509240314030400a000303182c0700d18600100c9131403030382c01445030385d0894005888040a101480482403050105540000240441040b0210050781d003440070240380c1c1c2400054141c80e5040a4400b8126510766401c020064801024800c44151403034045520590040021484440380011011203041c240e000d1491103040c0f0ba5000b24040d01a0000c02d01c8801c0e14140400c030380d440d60100308181400f0321074280d194403901d1071608100503c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 837833534 1250 837832284 837832309
    0x61e0207200d030e061c02090906010212160c0e1e0a020c070501050306042403050105221e0b0c04180516050c1207030e030c041a061c09050d02120403030c02 69
    0x18171803030522100203031700240700040c04680c40c005940000e5250741440e0001200c2c2d0800001e00c01403c59034944c4075031010f1841000155041e40d124100080d0820038455100c2000c0c200c03514140c5e0890408002e6080344c40d0488a81c2c0908a504200142c05100203109407400007045500030201c131841c041c01541c0702d03400500030541154940294030229004080941e10181290040700d40381d5183d42896402c5910150118540c08255140211035203858101401d8140d00a03100c0421801e0920a00380401c00da214001c20032281c0710f08000403a542980a0800c9650782020062858940d10380c11049807400c9035105503040c07c1c00100180d0900c03030702c00742c910780612004943c40c01019003401c0025030000d400450004054001e0540b082c1014003a010065005442c02c0c049010440341c0701400e40000c20701c40b409800d021603420010026400311071600303171300030704104144c101c01e04001d0b440321020182074000d44030312a0140403480e5007804850460340c040d0388855024040b40d007000355244219 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 837834784 1250 837833534 837833539
    0xc030a0b0a150914090d050f0a030b01110703060c11030c070e04390504020703020c22110703031514130e19050c030a05060c07061e0207200d030e 64
    0x41d42c1c0807884000510035485401250f0340c001d0340620340480e015150200c80082c410800100b80712160746032408400b6602c000b1503c0c04c02044000e450401201d13900069461100c0c035108020001082c0021a07004108107016580c4100d11003074210249503a0b441200360442c00d0360f010b041e00300000700c204140e00c0d8102c0d200f1343d03502910110a402c1c400e00520340c98421955558210076410b840d05030070f0140ca00812040e2400d43c145122610041c0d10b40c03a22040c280d00440f80242a2002521842c1c03d40001010030b49081003e450211545042c0d6000703100101c01003460280302c01c80840c3c80c00303116822640f08001c0c5030b012070120030501541d01701c3c02c288500e103103448000c60740c40d01c442400400301c14590980110084980f60a0003460511041e1046029401400110340460303400705025611030032118480c0d6030761084e0718040c4020081a90318410440d001d4900c6d400740480354005084145c024021041c09070b07900000c2042020500020540c01107603840100000390003280e1010303280200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 837836034 1250 837834784 837834821
    0xf031e1805251a1c050901060f05030a02102c1e0a120204020421170c12031302030102070b0703050105030616030c0905040609090b09030304020a030f0c0503030a03020406020c030a0b0a 81
    0x70010300c41c040703801000707004130b640c0d1100100030382d26000340300d0341c00140780b180d1240e05c1e00340c503010100340c6960358044064003a1071120003030350300a4002e00e504e01c03409081d01120031184a080806100c606401924984609031003030b4003d50028501c2d442c907412810081400401c41d14008202c8201125185c0480e00f0030307004c0c0b00008465111500303407415001c80d24400c40641c1d05d64940030040c0f90b03049041c181079460501c1481415000020040314140301030141d141ea0342c882c1c5c400a07482e0b01d1013000082d415800001ea0004000700589250f019041c542c03010b203e5a42c03100100750b2184003c5070b6140c0342d041c1132030348052003d1081d004104108602e040c840c02840d03c44000c03d054030020b40261101c0c81c3c5a0441c1c501300b100d8102c4060f0320000c43c4014504604095002511403480c40c440500310446403c154814444040c0903900140740090440350786403450b0102074040e4109100310b8003d4002e070203002e40c140c00e004c6030603040e42da84000d01d80c0e4140d07612217080004100d9504d210155811 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 837837284 1250 837836034 837836047
    0x11d0a0e03040f0303111f0e0106030203030c030405091303020a0f1505160216080d0c0203280b070507050a06020d06080f0f1603030f031e1805251a 65
    0x303080c4010700180112100640d295401c6041c0901072459408010546038800d00d001d0100e0303820802e020176221070070340c004605103054540003409480503403c045d605000c000b5000c01011800401841201c0742540d40520036030b980310341901c0f1250b01c2d0710f029000d600006040c00004002075211407174281301d140c2c1010240150000c03802241c80071100314201d940070440700c0ca0072070f80401184c1c81274225002d000d002c1c9030900c160745403101c54141011003408581c80a410031590107110108100d44407050303507540002d02e00c0e5401020200c0700010f592420440011400d064401c01c200d4039054ac0000080c11050200d40c0d0f803d00070340c024041c20018aa4070318000c5a0203070b003401449102800500200a541410104941422803903000c170820341c61412820030000350401c00782064148076040000d00040082c00510382e24405001c5441c1403450625407024102d00c010f502c2c1c01950064045075031010201d42c0b00400c90328044410100b2018143c1c04001a25004108800c0030b801110010304061 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 837838534 1250 837837284 837837311
    0x105090109090216030210230a0603080c0304061202041419050a03030c0c0609271107050f060901110904090c1a040617130b090f120a1403011d0a 64
    0x200213403c102d1000f00c0400d1042d003416410403900341e41e148030882c00c02c0049644101c000c0c6030914101d1400c481c4100b400001c00500e074030780c0001d0045810410840d40c500c800039010b9120780c8580640008510b680e01d2500c0c0070281442590241c1b00040c400b1414428400b08000540701703800069144074046a074089a1030f1110b0413180700541c429100d1820a04c914034100c03c000c00c0c01c0d00000c0402019080401419254000b0b03100c119503044102000c2d015aa05010040c0c100c07141c50840c20000003a61100300480090300c1e007079642200f401d030344041d20307140c410b40c0c2070f543e00c40079400d003002c000d1244070004c0c5065481b404a4920402c510f80d4407030b550303c1112038012100c1c4034074107a0000208040003640e400400b003115800401013051400d1078140c0c100310385102219000707001040206c00013044003500b080341d080c220500504484c1107036820001c0000315030091f240040050400b240e003440e4806098113503810703510a6603c0e51040c048102d0420820b070401841001401d0315001200f0488 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 837839784 1250 837838534 837838537
    0x60201050f0a020702030c100201090213110f030c19050405180603071401030608012c15040f113001150603020c120304050c01090e1303031a150301090c050c030901050901090902 78
    0x24808c0d400101e0946524010080c0c50b4002c4061304c400c581c1046080c2d40d11100c1c075400c8611451030748141da51a91100070003504a8003500c0c0c4002c82c40c028541e0303200800d1380c0010103001200d000b01c03202652a46111b6091500010076100540c056010030320a0041049205c00b0b071140f05018076001800701c3da264156420755490101c903041000303200903c20821012500904c0031010114010705190100c41c248614215005001070600380b40991404200b280112040e5843e0038001c064962600c001ca251403a14011031100b001e200303102913852602c1d41818094000070700700c0006541809485c004040c0c000c0d45c0100b0304040d5501800c025000300021005c051030149000300000c0c0481c0da0f941c0c002404203d003e4100c484072807031802c10856200c540350020241d003503040c0740c08105a10700104542c018100710050551140c030141e403076042e81280c50080c41c1240c09010013802008070204042e2490705c215108008150001c2100c0151940030ba80101260107040c034020301c14581e9031203120100e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 837841034 1250 837839784 837839809
    0x6010302070c26060a0b122404020f040509010506010207080a031e0509030a050102070c0b0429040536102102060a030c03050106111018060c18060201050f0a020702030c 74
    0x94079910000003405051005210700041403003030040011070205100e100a18076560000c56280740d249000a08542f100784000300d018501410034040f03810040340c080c2c080d09003220304500522030b04100041c41d04000600000313082c0c060f101c1003101502c80c40d003d11001c4240c5002010b02c1401c00034041c11381c60401c034a10300a40540e00058881c3c0507440c1141c030030191036011092012041c0820301a070751800031404143e48011000f2060003415807070a401a020301d40c00700c1d42c405640602000080480400f000c4500001c0040240d64101801407004400b02900c0c0b840940134000800d00000000350810742001d0860783d070513a01c005040e0b0004020340e010700c10b0390740040e031500703182103030342c0e400d4001c0c80c0c050701180c10000e8002d00c048842d41d40d10b0591400303401c05641c8500700200311998401e0000c041541004042c0985440004041c1c0782a8540d00345c003c810040c41341c001121481886203078060380d54100d4280c1c10741c550181c010042d401c81300090b40d0500900f41c0c8029070b40c0c0d40407a442c41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 837842284 1250 837841034 837841051
    0x40b0703050a0c35091005010801110412020a08011107060b2b0501060b030709180917130504090f030822230a030801090f020c0a0b040314030c0405040506010302070c2606 75
    0x48006200030b11b01c00b03944041c1e11001c001e03810f00b0240080e40d03000d4000d45040d90411241600c01b800b40d4000204a00003603400b11045505e0451040c041d141401c2c000c12009008020074850100d070074003440000c4036596860315480700340d241030803928002d0900c21510b0300d010b1000400c0c001d44540d10f4401c40c1d442590030b140450700d044002c0100c030171721440074000690f01c26030420a9514607162982c034000c400030204603020000900940380c01c4003001c0400605005481000707001642e10300147c0311318504609902140341000015030500300c0c2c101d46240f4503481701c1a1000c410f000da442c0408014020210414403000506c1e26900310400c2003015440b500a68441d10694541080202110400100c0c448124010068a20408000039170b120045a0100c1b010629645906045454520440c04407240b00340c0003083c0300d19020307903d000c0d00a8a100711410000740d15648010340480c401c00030010316504410f0000c1140416481c50448a1107800c194200003035130400240741084421501c410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 837843534 1250 837842284 837842293
    0x1e0317090f0f0a05040c03020c1e2a04180b0f06040e0c010c300e01120e1c140a020a14010c0203040e0c0f03040b0703050a0c3509 57
    0x400d4904411100301c0346005440700200c603102d507004640c080d5103a00030a402030b0b480300c8098601c14030a034110b03004001d030042542d40b100b81c2c0300f0b404048200c3d91100107000e4424510062692004405c0f1309035801c4072492000c4051045109000280091740e001101411043c0d680300041404090420b10620140d01502401e180220800003141c0c143c00c4100c050f98440811400f40e40d82003400351014a0b0403a0b40a1044040c444024803000c4d50301e04510030001041500b001c69507004114000006000d80764a4421045c281c1500219480907190302802c0c0d00281460b1429950354a111100405510341400c815480181e005260b52020b00c0c05e80041e4407404502d018814141d4103860b1800c4404000d10107144003da00a64a010741d0044003204c0050b0000f0030000d0781808100c1d030454078039091031030300d83c90182060b403445102250580c01081c24900041d089548900c112540300c0d125407a1101110020a6102c40311a00d4251a854588003000a1400d180b4034040842c0b1a0000c1802032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 837844784 1250 837843534 837843547
    0x7030b0a090204120b061203040807030c0503211c05130213050f070815031507030b03161a09030604051c09051813060e0c010e06070209011e0317 64
    0x304034614103a1041c4000792040c88203105050704020714007203440d004007034012140c50b48000102182009102902c10f8440010001011400440c24038210f80c040c0d0a000e103200d642d8414075440744009882107003040c0c0501d41040900c2d010402402c144c150300c17404142035051940c0b00c00d046a80986001e08002c4011598604500c1d001082c00031441c205007051103141020f0455084248002d0414014008903000141c5440d00d000c1d91591000401402c1742c142442c42410b0582840e0142d45000000c2d060209130081410005262004091580701c0f2801132454002d840300200d40307440c101d44280d001040310307020f541d608005160060b40940f01611fa01160100c6408071095403d0360b510920480750020011350740d40302c032002140740103800b40716029651400020610f0340403010050045203020b148140003000084c1150410100ba01c66078010607500003000010b00403448025800341c0c028006000302403105001c0c1c1044c203080c04140c0300490302d0344d0300e040410740001c0c0c1001c0e900c440407615 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 837846034 1250 837844784 837844789
    0x20f210703030b033012040b1902030c0310060e09010323011d07060903051b0d0605151002011e020f07020604080d03060f081c02070f080c040f0c08130302100507030b 73
    0x30317000b0106541859403030020030090480301d51000600c0607103ca14a4800a540f00c03401444240040d1846a4215903d00e8220f914a045810543d060051183e00c581c000c41c080d4041e042400c45404004c2000c9056071960750340744201105444039001c0107004181402a44409000c4c170101210201c4410a0608451000c2d40c640300c055030046041181840d41000400c1000c1005900b60340301502c0c0c0d5042000c1c21002c44d1222a110700d0042c40c0c545880100a0707408040c24101402410880e07150440041c0a2422400e0b034920a03041309201742007110580141c00320364024288481c0c008040360501a180d0005402030700250700080b0320360031a0f9000001c955240c80fa40d00581074403107a01841c3e6003000c1c0040d60b0341810005c40112611940200e20034640208001c00040c0780440480840039119604d031f5407035401d0306d100c50340620f00303000200b0100c09540c0135064401680d84d440e40321540d281a00002500d9000c2001d07000d5000d440f412111254180c016140325038210348000c0740d8208004107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 837847284 1250 837846034 837846103
    0x204170c010c060b0a120605060108090c060406030e0a050321010b1204230105010605120c090108161806030b10030905030d2712020f210703030b03 65
    0x241884a03800515180d4401c0c1e80105080c002c0720b42003800099550026000b00e44000011381006450004c2000340304200015508014800e00b4281c5e910382240c1c0300c0c8012180c5e02c45a440d003540c2c0c01801070006010007482a405000d00c220202c0c1200c120b4030542c0c032000c2c21944000d5400c81801d21400301c0c41004000800c4080c01001c100c070000385404460001c8050090015100400400ca06a5a1416100350803403001d4805a208000c1000e940d460030003034482d80c00f4072040c7c1d4403141030344002980c03480200150f800039a010385800350340e5a2103507016941400810074210a20150300e03010104050100b0700700020f0a81502c000400b68100001c2000c0446202021030825003003061510000f0001700036540c02e10480ca0b00450141910000c0c140e0038000c84130104441e0711010451400d01c07002103840c0c4030020403502600c1400c210050543c1d2200d0000091115070034080d030214080c1c694840082a00c0d50003031a0004103032014034002030801c1007040e1414016082c1e030812402141d800c0d030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 837848534 1250 837847284 837847319
    0x70e0a06021c030b040207020a0906081207020604051216030501200711040b01030b0904050c1f0504030803071b2105040f14190308071a090a0f050c130204 68
    0x7490103038003480500749000c001d5050003040513294070b4291502d440c1c580580300e6a650083c0300030240c0351036440c25002003a0302d1003500344074402c914262000c4010350049400194001d071201e4034050400e0305000107034070700f40c008000b58450b0a042c18410492901c050020b1441040007180c06108214a894480707048122006140002c01c008000500c0340b4421301c402d08400d42d00030841d001d042c2c005a0040607065103042c1c003c2600d008020400501080095214a00b150750150100c01c1d1100f112200bd0f0084004021540401090000c2800b0038080c40d0f003c00a0316007100090004595040800c44242c8111840140585902660405055000c0003640309103002410640381c01c1000d445072080e8403d5080c04090844c4540f074170785508421030130300190f403004001070a5485c40c218620b9405581c00395001628481110390a50395083c4450003099008020003010f105901d58107646102c2000c02c83d841c4c0304510700001c003612500f507808100c480c04080140c0752032800700110764181100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 837849784 1250 837848534 837848537
    0x1e070c05060306010503131b170105070314042a0e310311150c030108010e0304030f290703020c0f0705060a0815060d0b10080c041a0909070e0a06 64
    0x920402800e079a02506aaa0194207c0c012003500c0c0c1d0503042032071411244070000003c52441c00c5000c00c132004079281100061300c060008102503a500744089040700d2580c1004800810b1920215002c9040f00602d820141d00320584981c003040392424071400945c5591001c040e650300d076010000300b01507854605842141c810401c182c1d038529084c0356200138100354002420311040c030404090080042044215440004040f17001c0360400a0b80c00c1c1d0340340c00c244a02140bd40c200f01c0700205804012040d5021241d101810132040c000c1e503950b00c040345100f01e03807042004d4800d61070883c1c03980d1905e008034000d01c0f6031b481c0143c0d5a00c5c02101107041414602c105042980701680422151703c890b001c45a03480e006c0c0c40c0081258035030030381241a003206c141c00150b004101007a4059024002c0e030002d000d4a81c102c9150028a01c001c90540755044115150156003200340000c014004141c0c0d20140e81b00c003d00483d601e8810218002442c4c1e035001e66002c00002c1708e03801c000205090101d01000542001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 837851034 1250 837849784 837849787
    0x60f0504050601090803040b0708090d060501170f10020d1b0e131a061c06030c1530060801090b09060912091306030209040f0b01050f01050702151e070c0506 69
    0x800343c0e0290f51f0701c101c1c450206400f1000031003a0030301400105885107d00000e00310740450300f0a05050700501400c1c0500c0d0460390700c0040410380610b0004a0100040b50f1002401a60b0f03011401c1e40c00a41007907510640c0c482c2c42e401c411380120a0740c40742c0d00820440781c0f5551081c100400078040f1141803000d01080a80c03401d50010f09140400300c0034010008100c0c0c15903590701c0130b808854040302c5e16111800b0352600b0300c00003004021b5404c1c2c4031001d0f6811340c0c1c2d81c440d40808010088609660f40e5810805002d178030315000702c0031601c2d1600441d00340c20004020582030380e18200d20b402c42c3d0703684000b962031041a2091111007e024001d5a8015100100400401d030750817030742c4242441071011107445004007802105000e0029080704005607002010060307940713800d085c2031440f200d00b1442242c105111200200e000d01c0e00045204945006a41e0242048025402c1c0030912400500340e6000742c0b000c3c00b80782c4c400c108403600c0e046202981140643c90703849c2407a0420b07218280f41c20480c4500c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 837852284 1250 837851034 837851039
    0x130e09070e0c03100302060a02060a05060d0b070807110d121b14030912031f360f11040f08010209132d0b03190f2301060f050405060109 60
    0x707031008031508440d9290202e0740d01d80ba4448202601d92a55000a40018000c0340211201e5004500c0b0307031007642d090034180308690360f480400111000104005003408400d83c00314050b14402c1d42c0e9694842e0081c20302900c0104000100b9242889001c01003002074100c00e170722080000c2c24000c814080311a40240c00310240b4002d00985032210300b40e86090030713410200004440c10000c00c1341103103140344d0800b039a982e81096840c100206007020300184070f0784003152000680c1c40c2c2049030b54048040030b5950b0108035600c45510b4111115043d420000036494982d0a4800403091080f408000f011208050360786241000c40e40c00d120550b84010f4942e4410322072003c20340c90744c06441030180102040050103000180080040d2840307000700b50428984220342c45000000c03075012a52030f0310f0442c100ea2138050400d400702ea401d064248000e01e400401091200041d104d1009800d854440c0a05400320203a14002e0a08540190380007682c268246802040242490320460303070442400c0ca4141c13242070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 837853534 1250 837852284 837852299
    0x120c12110907051312140a0c120809100806010831080c0709060f08070510030917030903030403030c1b030e0f12030705060609090d1b0503130e0907 65
    0x55580000d01e00814850000a250b184074000300c801c0b4400b0040511521034a56040d070031243c00743e11040741c900010f81084040c00380c0000e07985640c2c9a10407961000303d41420030b181c2403400c000e071044034428801d00107411103a0f40c403209030018079520303902c1d400285002d02c0010007815000d0b2007189094019500c1507003042c0400c4540115008800c01003032210210714181a8510030000e00100b180a07003e8081162102034200070700700c521020761040c0240e140c06141c0e444100b03030700c81d56602003508100c0e00f41d01c60290704200000c5028802c0001c0e241d09540c1010000ea200311455100f94100008100400da018070850350301c06442d1510300c80b80103410551300512410045e01800744001c0c41e050b245e89503250450300300c250001409034000d030034a480c41c4a58982140008442034015100094501e05111240902c2204604010704010070317900400e0700c004054001401040b2a0b003181c2c440455001c00040001100c82e81d10200c103d403a00c103000540e40400b0340307050000d401001042101a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 837854784 1250 837853534 837853553
    0x50a110411120103020d141f0b0102010c091e030b090102030601021b060901030f0e01060308070c09200a05190e03011116060e0f010903171f1809020a120c12 69
    0x1217505445c21050030182d81460a071280c1d10301c40a0800d84201c1e08031450f9044500100b14070035280d20350510850784981c0041e0709079401050750344001440c0318000c1021500e0600404080d2550401c0303220300e40d88980f84d48102c40c40848110029a4000047c402656410458068045a0051288400280d00000403990300c5030082d400d040680300c0402507070380c580e2540300011211045008112a6941c0e28007542c2540080d0300a8a0400030440002607a6000c0c0c041e480540d182454000440d0b8240300c4420095001210b014040003000d10010310301d50411506410226500d03124141c00d0750488082500b920b081e40d80b510315103c0d06103d00b03c0254070726081d42c0baa45501c03143c04a00d001051030014908a40d08441500340d40c2000d03022410306801a0b260400d004aa080c40c0003150b650402c8511103aa09400340031a07444481d00c200000e03812256441e0444e40716000100d0000783d2a0009682d0301b00e03e4000c00c2013043c2c00e10b008810003a0f091403200080c0700014040d200c905c80740c1c8a80e401c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 837856034 1250 837854784 837854789
    0x3180304030209160e12070602010e0114071b02270a0e0c040b0301110a051c0b0a0b0306030309040f06090e240402060c0a06020a031a0904060216050a1104111201 71
    0x3c0e0381e1109002d030340b00f401317032800b250003007000780c50013070050032990391517941d55080d12644d000f65103030440942900106018800c00001e0105000d00705450301074044a154000030300055515081144a0340142d170340d61035003805215200c00d1030303081001e40351409040d000f0181c0f40925480c58807001005411010421211070032040710000354042020300424058190142d03441c20038540020b82c46079903030700800540700010552400391b030542d80b005502d108580d8600340c010361103070301d00303c0c2009080382c2c040003903500035030150581c0d081104210104041d1460b05029160320b41d00d41030705119200a03442006501079684009010307a400d0022240d40c002c80420f481480100040300180542d10388500b103500c40c20b000403c0f42c45401c56414010000e4000c102c001000a0502e1081c0140c24545803c0348906e11004040f11500c0c0c0b2182e5450000798403262240c00305400741c401d10004030b1010302806d80418001c0302c400c106030106000300401c5411034000d4000b1040b00f4041c1a55142164002c0b030305 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 837857284 1250 837856034 837856051
    0xe0a02031f0b090a15060903050c06030c040e09010b040c26071b2a0b1b010618090c0e043503070f1403153303180304030209 55
    0x440080034a102000341c01d9030031040380c200c82d01c102488a0b071303138860b88002d8840ca08000750119440c0c0307580044510051070700c009080b0764803041d004440c601d07107500110b800c0701d51140402c0c50a1351714400d954610504540102140e5551b0f1180e000070b041c9801241103403100b070301d070040781c65188080280c040c6440c24000c3c09006d0b14040019503060082e12100015103450f40c10b01e04803001071500c84080b000000c00b081c00480c50b60029185c130700320014000d040d9140122924100b00407020544c9181808480019142d1b4941c04002090304840c100443c0c2d0070104038005c40d2310211800d040002c80c10940c0015040c041010420001c03592080e40301e00403496540080074000e620445004650190300b198900110000081c0f040e40c07a0804031540e1908603603204c4608410300001d126000340400c4560710343c030400282c4111030524152689107403010090303801c41050380000400d181180d41126009600c1c14000081c0044004074000300c14001004c44d004519260950307001ca620f19030050b00404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 837858534 1250 837857284 837857323
    0x16030f060b040308070c1d130218011d060604060f050c0304090f0921080a0b031e010b0102100b0303040b031e0709140409050a110d0813090e0a0203 65
    0x82015040d04000300401c10040003944850326401c00c4400c5600103201114507881030303440002c5203040301202ea8442207140c0e142c04c03816a1545411261011940d07130803a441050811005450500180000d000c1d01c03128140c05503045c1d014811103294078014040d0f134800c00060100b0000079900ca8003480c2c0b044018030b0b01d141c88102c00f0201d149103001e9074002c000d5441c100709144560f01e004c1d07880110541d004281550343d04141d52080d1050340406a9505c0019241c1400140003810036048801c814502804440f90302c101c45049603241c00d10140105243d945454810302c40b5a4100404a40000d04440402904408400117580c0b4405c5100c0e2202c0b4a2020000441c139994006118000342e0f00550000020720b0500030003002002c0300d0080427007500300b1491070081810140701e980065588180104500380aa0b180d04418840000b4080d502c0915255000300280d481000b501c0d02c6020090048080760034001c80703a00340d8108541c891402d40c000c4030304c0409640c0000720200545100380488 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 837859784 1250 837858534 837858551
    0x607030c0908031804050f06090c030603031e0c120f1e042301020d0527060c0717060a02070302030a0f260103170403171c1805010609051603 62
    0x151480c004552002c1d0300c502001c110050280c80003400000c4400040fa42000603940324401000c114400b51031040c6c0110b11030001680c9000017400640d0000c0c4010b040300e007060060303585110f0100120038203950303510010880100560041001510011617030100500301180320b9560700d128060500c540d003001c00e050750102c04800595044601524210150b8603070302010040c0c03128025003408107a401481020f0000c28428803c50554003c04500e01c401e10692041c068000c1d40010b40100c101d42c800c90401400415890411600c4014081115846050000703414418140318005051012407401003148200180d40402140c48205140c10700c6040511807250456098070584511210b5101102d21080c1e500c3c0d5403090141207920509240102c02003c58910322305000f06c1c071008100c50480c0c5800141e040041d0050015960508088468803080c00304c008180c07603111416130340701c0000b02144010b1120a02801c005031072484400e0155003010040700641104035a180001c259591429 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 837861034 1250 837859784 837859787
    0x303070803041a01091506020c100503091e0d0201050708100e1005090109020d0b040c2c0303030f09010b0f0913230616090302030714120111030a060503010e0607030c 73
    0x20080d800f54030a01c1d0020642c0c50b045040020041d070710028080c9416400c0010300c0d14030000f03a13001d04900c0640144004c103c1038005450303030b0f000617107041d80d140034181150220510100e10000a050b00d0720007001004006080a0708442001d4000002c01c440c26040180d01241c60880e00c0895000010140a5540300f0394070b03803101070154102d0780d88034001100000d402400c1c0c0c4c0160003070030003e16080041c8079501e410001252400c500c03400c0450205c071469524800d03034003541744d489405c8002c2c040381d55101100081c20b551088911028000c5450180b0100035024440c41400f040c0c2900c103810301025400018400da08001d0603e035440311a07080c02c1c010000400880f0003081c4904030f01c04c001d02d0f40120555290501100d20140042907405004082d80c8a00010421250050080c0030718038203261140901c0030011209a412000503240c0303401047c0244600d2042c0503801d8040380c1c0f03e0801804e01740607a440c2e907100c0d038480c1e030402e003105013034440101e42603400c450142000500e407848882c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 837862284 1250 837861034 837861053
    0x120801050a050f030f0f010f11040f15020a050f030a0f050315040c050702030a0f0311030a0504090f0615020109030305010b0c07090b0301230613061401120b15070501150302030307080304 82
    0x11203da601446d02180d180301015003000b0410710001005000e4150018842c0440380524819540c80c803604070320411003000e012503d26810174052050754103080c00c0d52280340c50700c006240900c50b1343e400020360002407030744611604c240040c1031901d54903500b0402541403a070703c001c60181e442642e56102060302240180203c0303880980c0601a68601c520038102400225a2144260041640075003c40f56601c004011905e514031180c80b958181410500d07003600905482843c543e266549035004100c11080d100304c124031024940c004100720348c9038500202590010303031003d01006028411404016400f0940d181030350540c0e040011030203000713800203000d000800300e0000901c00802c10319205140000b5980e100b904181c4100e00074206000c006c00480f1603070310501456002c02d1301180310729840350701d00074103c0341e01503070210f407071141c0600055100014034010241c01e480001c100041020a005645e803041c189509407a11a00d980c021907104e00c00c00b0801403034407800000140c1081a640f2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 837863534 1250 837862284 837862303
    0x406050711030724061d0a09031b02010c0609060209030c03010b1c02040207060c0c1118010b2209200313020607060609060902030f09060603030d0903110604030c120801050a050f03 79
    0x4003844560358034520103001412002010f148180840300054140d002c9001e88c400307580c0c1c9540c1d2440315402d020501d0500c00c150581c08c90401000340c245001140c400d0007070411660040000688d603010760410146050028941c140c0a41d060050b244499074640d07448400d80000c1c003641100c107041602c0007034024400c1100051141e4541600e554a041e03020600c14803191146a0303c8941c1440e50007000b400c076102d0384810440140100060040c20400c4d0064480354101c8508402c0106101ca50b0b01c003080f10f1741c0c00c44060f003541c0d00c011851200701d044950b2540140c0025941c42c504001142a121807076001e8080d000320000652070040010943c0b2840003003407440d40c1048a0354540d50341601030b50042c0c50345040303150b403100404c4006102050140c0642c500400551a007007400c081d15024081d505404d8052200700481558031400c14402c0a103d07601c66915a03000007040e291140d050503214207404100319950b00103010301e484403415074042c8d6404484d00c480f07000307800300080d10b0544d500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 837864784 1250 837863534 837863603
    0x5220314060603100509060103030509031518150c0f0901020a081602150310050907360f08061b0903011a030705030c030a0b092404060507110307 64
    0x540c11148400020545500602084081d207075051515101c0c2010385000350303500031554000400400019008030001c0c031448501900382c404000d40100c0c0318544400444000b086426424440e00341d05006202c2d0b5480022070070b44148c01421b144c01c200404d80110314121101c4100010a03441a80c000c22914100341d50005020f55611303076114a0040f10000440100e0103928255140e4118025030800d03030f440756001c40100710880745814104204030002601900c10302035100c6403006443c8004031140d46015115032a5400b8500300c5001140000566201c81e00300014407405104803031011500c0f07900866541c1e540c0d400b0310354800301c45140344034046203030794150310f01801044100040440800711800c02c409607009982d5039024941c8500c4290f01082d4590040491340c00007407008181d03d500401c180c000c54003041a140d41010345071034064030b0090100312510411041003028098180d0220b10b51400b1740c00b0120304018941c3d6406034103001040b1080300c0c2101a660480610146c0949259 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 837866034 1250 837864784 837864803
    0x151505030d050d0501050105040302010e040c1803050309032b080c042105010e01050106020a140325120e010903020904051203010b0c06130c0b1c0507051b070303052203 74
    0x246030014102d41d1003202101800c1e400c18000007080c0d80a0702c150350032a5010303180d4480340780c50b12040000400c015100070090100504480d2029040380e0314490156114030300459035150241d080514103041300359415200d65500500c1c01681d890200e44802980d4281012540c07a200c0b40105001401240c0005020b1030822501c06280780c4160040c910300c9004100070020101ea01500900340d0b8401d0080030007503400701e09040001a08803001d9080084480180c9040c400403031b41104440c812822800030b1070342d0410724201030103482d1245030505002810603901030448800068400304161101178803a09404001170b0a100040c8440e480b03188090302c42558941e151940160140c2285000c0d95007031145000146900c1881103003203652540060140201e070745401c1e0500c00c6075000500d0309002000d0310081424903006030203200e000382103a480c2e440d102c2055401038408070541c034156081c0c5522480041000c80d4102d811680700c2001e05d00c07000b6044210312000702020b0115031004000405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 837867284 1250 837866034 837866053
    0x806092208070503180f090702060112030c08030a020a1202030f04030309050c10090801060902090f040b030f03030a0207020f01020c22060308130e012306030601090504051302011b15150503 83
    0x540c1c0305001417014086400503021107498040c0134003e40110340003409070f070007103005115450b030070041200c0952107881c2c030088508040c0d81d00103494105440100090b500481c0022000390400c250729285000b00c4400c40c04c3d1318000ca9081d44820000e0006020301d651203280b541400028403400d10100c5016104540c903c2d01c0400041009810348a0120349510f429004900000c56000700c0340d5074031004040c405c1001032042000001c00118180c0f46d454804c07241701c600c00c02002e001551240903469401a1242054018400d042605001113811900086041c100759501c200d500e0321050303044610072007180d84601c2ca910040c00c0c9a00080c01540021a016160412600800066070511400102c60b40d984804515451072040c07401240d006440d0f45c5105141050005154004014500b000341c2c940d458000c2801c44100b078442507903c00c1403007031401c19960014081800783e00035001411900101d612502600000d4507241c214071501c07281e840391030201c05c98900000e45002000d580c07a140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 837868534 1250 837867284 837867307
    0x711060d02120f090d0f02070b0c030408070e0406150819110a0306150e010e160e04050a0902040b030309010c15061e1422020d0905030a020c010806092208070503 71
    0x504592010135440b49524010643e445040345400c1d00c0000c0e001422a203050494540041c3c0151440362401e100034040054150420051040101005c0da221a040d0030141401c0c019140002d01c0c404001c000420104009003000402445001d44070001e80c1100006160414001419104203540103030605804001e010031540000420807119900c01c950b1030b90340021050b0100248076005800c1021400600c4210130311400070b5688569140030f082c000c0302c1a00040480740140d540040f6250750b0a0381d1021800d03c0e206200d200b0000f10003c1d07082c0006900000d2180442000041c2024584080300e0b5180d146600420054900950540d1000d0004022240c1c0340c80d16114403409907007004510301c81428100101000b02145410303090030352480801070b0020350700c04224581d2842c1d83d010403401041041c00908010791103640034052690b5140d000420303410317024182c01d114040c07420500422280c441249100c2c2c4840b808178171800300c00d82c00c00204500864174041c280340400074140640d103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 837869784 1250 837868534 837868561
    0x106050915190602031e0c070609260714012c13050103120503130f050714010311120601090f08070303030f0b090612030913021e0711060d0212 63
    0x107040c00d552480c00940340c03100c0c0c400e540a06100301c40250704100003524001c101881001d07076603164500100d240c01d1074007940700e00d0504207030b001100003206940c0c2808040c0b039000501110b05407100c03d4141114145803929100c0e680c5105a0b44150a010f0035241564021348030718a9085a0303e0030b0b10b2040c0e0401b000e40e03088050350942c03e440b40c03036200702c0030f20426080c2c452241a690095682c5084545070682076565078405004a02048800680030001410207100300402d10302c2031000d0009140b8184c40c014648140490090502d0f06040e03004414034142ca080c0e4143e6122015020566203490b401a1141d01c01e542002130350029840300803868210000d03001c0308591082d9810000c01c0d11601c04001242c182070b44403a884000304000c6140d5103403088441c1c6075400d80009a1b4500703070001c40000e444204203102804081d0f00861050f20100442d00700d202c8102d00d21800341d01c0d0100340e03540c1c480c010001c050400d200d0b050100300740c160750035140d059400d400030700340c82c0d042c460619050000b04ca = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 837871034 1250 837869784 837869821
    0x9020f0c0f06010308030a02130506190813080d1a060a0f0207211709030f0a020a080f060406020c0c040e0f010b010908031209030909042607080301060503040501060509 74
    0x24455100380c0703055240c0c0010401d040b240c100d0030745401e58407509280380c0658007040c00c081c48c040841401140f59170314003004000c0305252041c00b8080d60003c5c0006011030400504511481c1d40d40715042011950000880d80203043c540e00000704000500c80d960342004014500c642c0005000c61207042c12a0001c60307503c100c001503000c480c1c0d540d40e100441180e00902842802c40b03000480c1111000685c1c1200c603031001e01b01031031514144030500c030100f894000001c2d50508103600408900302941894400c07030010b0030712540a00011000000d82554403400988010301551b800144c4110b8124180148400050001e00500ca000c1800e10b1442c1e89000000380c903003265117040e18951300f40d0f02881034032089440c075402446c180780702c101c0e01c41c14030180100309404601082041110a98880707003030610680c41041c0100000c1c3e03404066108c00140340d60001080030080003058045074140003940d04603503003482c0c041d80e250f40700d26051f405050150700c0240c01c40f881109100d851804035105002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 837872284 1250 837871034 837871057
    0x16030b09010f0605060f09221a03060f040b0907031209081501060f0c02010e0d05010203070206160e1c0c140f0103060317071e060506040c08090715020709020f 70
    0x2c42000c941c03010341200e00b82d104280d4030040801c11600c219046c03001400d00982c0040c0319408a5404440e01d0300300d020310442054803560744420a80112580e580041c01d00c07032091703005042c0380c640307503411111710f0b0b80c09840030381403034a4000010180a01003102038040c691145408894a00c03810001e00400b502e03000e0600d940c09040380c5400d0600c3c120340814122071807903513681d03e00c9a411000b6500f4100401040c1d0402000002002480d01c80e905e80c3c1c00c09510032800165203180c076600080c241030001d002d40312140052154580076aa1042840040b104101c84001c0d2465142c84005001045124000c250b0640d900c030028180740d40c004045080d80c030685559020011800c011001c031842e601004004117202c003644100c01039198043c0013124425808001441c000d405c80c9180e413000c41c001150303071a4039841004030f281014000c00007111759500b4590103078204800031580f0703001c040c0191803140d01d071980c400003c28030030017001c8002d00803040215901c0a01102c00d01c03090340507411028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 837873534 1250 837872284 837872291
    0x2307030f030507021c11100612020a05011d091e070207061b0215030901110c01020301030c050d110103051b220b030f01121506060206180105010807090e16030b0901 72
    0x107003101d00100318a03017003007104100040011a0f2590540f80d00c2c50440001340a03108164801e0700c003400d1440b61502900690450000940c0288108448802e030350300058104901503e041d402c204040d4002000d40c042101c6448090381d540502c1529080d00c0550450019623207400c0c84040c4d0307000314500341558410340e00c050305214410701008a40c4040d200094004100c03005243e800c0c00b00c14003450f000031400c0e0011a0601c0c140c00b00c4515604800c0302c2049031396000004200f082407840348000100402d070303030100f8030140d152540041010302d11085410b0640700c0c00011600c00b00c4201c041040160300f4405a02c42c041501860181d100150158040c54403d007008960f0001000036a8424000b4002012503682071450503c88400d004008940e904049582c52508a00b640220748c043c3c0766a50040400d4a00300d10941c80092344800100140d17454000180802c2d030000c102002038803035044021803021641d6038200d00d0b000a40c0280c00c007803c009080403040144581c1050b0142128400a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 837874784 1250 837873534 837873541
    0xe2a0a051b0601210507050d0812070206060f09040606090203011509121e0503040503100203070219080901031d0105070f17010509060d05030c060c1b030c030403032307030f0305 78
    0x41e42e44820038011407226a040141444c14001e90051841c0c08078420410780d40750568850100e00100c082c1c1c0f90450303800e100131500d03100f582d00489006a21840a00c010300150404030701141166800110550195544500180074409560030080041c040d518003150f9075a0b4640a04001204101c5248005416188000340400840e000ca00b40190002028951400703400022411543c4680044030280002c0c000003074a5503040c866228030181c407200160307030392818103002410240d9010310524166052044000468480415130b01d054070282000541b14500c00807039407204c070000d8050b075115801c05003001000b5a02070208218a40035403a120f00202c040e6001c1000041c09000381a005007840740000d619281c8910010070352805501030b00d14241c0340a40e070360b0410f102210b10b9100490002084044079540c1030600c091905104051400c040b04074629544a104511000d000c101d852109802c914803c1d12285c4c101041d0491210f0742e03016030b0314000c1c1000320f0304801c120100e407421000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 837876034 1250 837874784 837874837
    0x150f160f080c1207110c06030f0a230a05070f02031201060e0103270b0609160309020d0b041a06060705070509040c0b0c0d12020304030c031d0a14030708070e2a0a05 72
    0x550b802000b102003840c4039070b0317117421040c00240703081c2d03d805501410242c20a41d0030440620040e01332074214801003694580b520025000c525168500d5046600c1080092252501003000742d040d94024905008e60126843c012005000403290a0340100c1c881c090600e08404440c01a0407118459007e00180e40e4070001008000c0038212000000c00ca181c06501c48071920030342c031804103a403005058555000060b220b54000d5001250100ca05004251207603900c1400651140c0d8804001c4525620f4100c055641c0c94482d8507510034a4054410030740850100403180c40664054000044442e03200c1e00104100fa81d80c1c011041e841020031080c4071414810440303802140d01c10764160300c50700c005040c00d58086602c40002c1e81c101c61850000901940140d6032260140020b0061644501d86040c0c03640c02c06040c01c40b16130001d1510b5000359010400580e044c901c00c2d61111018a007100340c40d11000c1080403003544041d01107100000014040d0480d900f0202901021066840b0800203806480c403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 837877284 1250 837876034 837876037
    0xa081c08011206020a17130b0a0e190503210f10031101050922020705010509030408060f0405031c020309011803051e0705150f160f080c1207110c06 65
    0xc044a0301024052040880c00c3c640040880c4589440c015190b9032860380815001801500e82c2100504d415250400303000c00c00100c81d4111078150010020140f00e800d01c25a100140c01c00240034048500d10340d000d100c001d006843c9409c090311520140300c1c030307440000000100c0c00c41c1d60564200b01240407800d2103841a0000040e00d44c0300c890580c222a8a40040d580c54204002c210352108007004030381500700b81518240c4110007102000358407944549030140c2591030003080500140d1091004000b0a00009031894220f48000058409501c881c01c140e411413280e40345031803003c5200c0d03550601e0b941440e802103100703100d0b080c02080008184030003c0e00c200091580580040c4040c41500c120076002200ba00e098075080000c07518104175592110f080841d4010801e8400480d10100a40e1030700c184407160340020411480a52070920700070190403440c04005240401440c00c0001750700710300003801c81d001d02d10400c21180030751610b03010003440c0f01c801c0310034041c0900501d001d808c46810880c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 837878534 1250 837877284 837877289
    0xe012619060e1305190203071a070c080313091406010f200703121706010e130f052a03130201090306140115050f0915040e0c09180f061002010b0a081c0801 68
    0xb0080e2031060320b880c0c5103032019149c40520000e81c242c100003040025000b4912000104810405181c880d050001c40d48043e0907994082c50480d41842d03681e81030140041c1c4d55680c0148d0034207100b90b20000e000790450f080ca00740d0343c0182044592180d0300b100b20800290b140c0460f407041240d611403500c1c2082c01c61708809a02034032491400c0c01804104258045c040b03207800887c010b09640d40720700f40c0818140039181c0c2c00e0245910b03e95948148070f1000c18103003100001079250280c040c80444004040c60061200070035502810040400c0c11046a20611000340156003201d4103201c00d00d82d20100031480c0d8800c0c414034a4032486a10380c4203180780103034150390070200c4c803880250a000b0000284600183d004040d03203001c003400c00c00441c0a1150703020390350089561010564841101c1070a000c00c484190003051000e00c2d46000300a1120b03c03001045a0003c401d0320002c00000520a06030b0240ca00c0000d4140c2c0185030f004003185031000003034107400e0708003003c5600d640900c103c507082d5406082070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 837879784 1250 837878534 837878539
    0x3170705240402040c1e030608061308040603020f04030c080f010b01090f0e0a0e0d20070e06011805090109150509062107080304060e012619060e13051902 68
    0x14070025016140c41d41c015407858505007081d1880070641c428100c80341d44503030700341c0010aa48000c14800d00d5020841558801d034a0030450044d88020b0316a80d910340194411070041540000e081d05c5401610380642c1d009637400303040e0007040d60301d9540d91a00d13000c2641a010700740d880d1900c41c050f90b601ca10901070840d000030740d10b03c8030582083c0a02ca4100d000400c0040c104e80c40c0c007850359070b64604000300564200c0350f590324080d0b03800404001c6803a54a000f542d04540d8009141442900c11031949103400c40c5090a04056a8841643ca1400043c031603200c9a40440c2032000090141c0c01a040380000c034495401540419490380c0420580300c000f5076801da00b146650b030543c0d008411283c40e030b04107008600115003a175555080e106243d54000d4100800085600c1200e00c02941c010540c03840e9014111075503108404102ca140f2103090b401070440685074030103104039920140640c00b030b00140080c0d200f4211603281483e060348805224010031542031103101a04000c407104c0e41040248503900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 837881034 1250 837879784 837879853
    0x10e0f1005070201020a1e12031b0c11120d1223060a030b04030509123d051302031c020c010c031403130b010803040f0506031003170705 60
    0x4000c011141d079041110101e06600c510004031300400d0000a80315401d40a40356421000803483c40c065164103003401c06901454180b54030b04e00d24500d01c0682000c45040c43c0703415004103c0606021128444642106800015001302100b541c103010074444802030b40b988655080101064005040341c62442c90b840c0c00d54005050040c809420808081e001076004043d49030b200e850b503c482c80e11a1007660704801045000550140b00d0074040c0e64061403010310009000b8407100c0d8000402069500f180c41c5c40c2070b00c00c1c60840781c00da0050030700216006405900c00c201510b018551301c0301d8407070f1821060384213102e0800c42009014400b062040c458080d54050328241c41020019038184071155000c0b0140000200c0c901003a2a10901951040c00d02d60410b80700a959420548459001a00010000c0c1c00400c0103110300b11203109607000f00d500a0707404e160780e540d0b03040c81d98030a08880e400040042010410a02019000d130b00030740300d40c070f0142081c0d074a000107034004060313061002c10514140c401c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 837882284 1250 837881034 837881059
    0x30403020a1401031d0c04050c0a080f04060e0d0e03071203091a07141b03011b120f020720010206010e061003090203100609060b0906120a0209130902010e0f 69
    0x500c1c0064000e41c841c10304010965102035602d805d803072180400c14203042d41c010000400245064001c5542124035034200602c0c1034480c080091180000521900f02c6800c0d9402141c08c00c12280c1c05403c044010b682a80c0120b0141540180703034026100640f88a4400c00e01f011a216180d1200011015815202d0712405071034100c050310411003480d212500b03190203200b81f0004c101c011140c4440510044050002000040d1007005416529030445020b030785414070100c45060482060040b400e0030781090981134009807404030143c90b0307444294044500100740b41c0308011800c110900034030041103485c0190741c03d14004a03940c0c0704c24803d410206003c1c602041e40c5080943c410000700406182c0880d032942d03da00840d02d0038082e1001c07820119510001000307500c1542c07050801510315501c1d69840d03c110040000c00c42e018034500a0680140e04000c60008003032030381150046200a0200d41103031420746104d1f030081c840ca000a0707003c60f074040b03400c04488c42c0c1490342240345207009140d82440d11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 837883534 1250 837882284 837882299
    0x15050307092d02071b030b0a060b031302030309030a030e01110102030714071e0305090301200a26090304030c12020a091116051006061103030f041a09070e09030403020a 74
    0xc040e070000051082d82040300c0d501240c01c408045c5201001c803490002501e207185000341038900018071010f6400d18051007800803400c1c0d03908807900006070119a200322112400000d00703500c01c15055680c103110320038040d4105134205140301901c80702603c6500400084440003402c0c1e10048030b4460010380540600100d400254024250181c00707a090031071203585c1482100b1440e00484000d40210341c0108040005250900601c4407240840c0002070076081800c1c140340721809500070f18420b025030003408160443c0100780c900010884004807003400e042003811641c4075070081c041174881700f850140200340040d01140403510158041c10340c0010758545081c0d0300081511919403240020b04100c41030f41000051031038144140140b0140107410300b100001001c64080d0345c040c606220500e00c02d02400b1801100b42c07a0f00842c100d42d844402d683c5c5242030100884d82c07043e80074020b01e025003408110400001c101c000c0e00c0c880d219005681d192209819642e008034030000f580900d8900b0b003403086d40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 837884784 1250 837883534 837883601
    0x1912021b01140720040e0f1e0f06012309091c051317060624031302060712020622030315050a0b131d07031a041505030709 54
    0x1007860300d0800e0500603d65140100c11880283e41200c2044200c2461424585807003801522000840100000c02c802d590345515020000494241c160181c0019001180c05106800b680d0743c0c104261102c40da124144680d542e0030f04580b80740c41130300c051110941d500349450914040d1815000a00ca180081203440d60200070880c2500f007001401d2040030428082491224098032040084494040a511949191000060000e0b00c14002040d8071144d072514001d00c8002c0103200410240d880e610b85d0000d5011f2441840002d400c20800a1600284414400301c02e041c2c0074036034251481501c840000302110040040f900c01203079400980000040d0081c0e100030301d01003244c203110004a94400000e041102560b000c5040b0034400541201c3e0400c90019240c0074003801e4100503800d2880b888000c042c0a00203001a044c1961861008855092160302420742c141c0240f040c03084550ba020040c403401843c0c801c00c0d01900c100c03000450f260090b8046d000031700581c01c007180c605910700721001514 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 837886034 1250 837884784 837884807
    0xb061e1201060e07021f02030609070c050114180d0e01050f07020406180204080717071a090a0b13080f0a0314120115140c060a110c1912021b01 63
    0x40e40da14180082e42002c0002024421301290300a0040000c48030101c1140c0441e007840542014410020080aa81c82c0980d594101e0400e140c1010b00c03100034980f2a006000c141da0380100070320382c02c04002405000d8203150415903000c4c01a1000400344180c00e880c0c0e0180110243e02051041c80102c035021940740140c0304003400144041750f02541d450032a4200403c03645465541e0f40c0000b8144220001042298001c1031500c000b40e00c0400c1e42c140c2c0f83e1311140e01d4010901c0441660500c1882446100151030300c0c1003004040c0c042495032412081c07003650110080c0894405071010006900320041850b80301d100c036a01c00782c50034017441d540495500c0054110607188600500000c0282102c114180d80038005041c100500000181d001405010201940c007200840030007101c410004003081d0071703070400203c0401040f4460039a00c6400c6500400981d403229128840e1940a82000c050204106600942030b8811250301005c0407030319610042c50f101070b4281c42d80712003040755105900c144030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 837887284 1250 837886034 837886069
    0x40f02041107020604030501050a0b09040b0f040309180606090603020f12040c030f0c09110403051e19050a12030e0601140112020a030c111b12030904180b061e 70
    0x142c80e045900045071038100d60003d40704c0342e5448040049441c120b1040d0383d50880200c4504400b0301e003c3c0c1c1e4020588100800d03000700002d80b07030301260805018580d43d2014207404601e4210301400241160000c0110384103400020f84261400502a03003e4422518900001b42c203d5240c041ea42030060828000900111140820b4250000105250000d00e14a09104031880a141403030204007100b41c5480214441060400300070400c0000d03000140010088100c0c03440700c0d419202d0b07020941c1170503840703022440c003800710304c541c1020441c0118098610a201e20340301c44c1d040301d903400100c08555400310510103542c4400014440d21240d894005a10101490503072a681ca00a4096090303030000f071442030229456505c0c0c2c584441c0c0043c4481c0201486200074080c5c2500480b90038000e0701221045401034803e83d181c40070090007403007281c0070320030060801d02203d620080811442c0700d09440a0361803030072040100d40b04d807420380009500c40070000b540031162011002004200408500d9030007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 837888534 1250 837887284 837887287
    0x4060e060f090405010b031006050406051206030f0f0703060f060f030206031302040612030806010e100e010e030d0e011d090c030a0905060403050306042406200f0c01030e06040f020411 81
    0xb4290f6594094240038101607003980b034403820010300c4038810f4070300c40d04004103101091005000300d07075001c01502d264003107041c1d00c2d021a03281c5601280c204038800000d000f65000311340c0c2c0140342c0c080000e020700490784503140c00c0251107101c40c4004102c408901654800b009401c004001616110003d0b43c2c0102109006640c102501d5001a080b58000d51050400e8802d08580e51f06160704000f0710740d0300001c20300700306041040c3d980000d03151040b40c0d0609802d000c41c045580c40d240e40718088070350329002d0190071030700c8411001d10301500051320401401c0c0020340f11a00b40e11501c0e031501d040c0c1d500d01d1000e44010312517281c8203000d0b0143c0c0c200801c2c00074010b0ba0381440b200410020000540100c0c0a03031211541c80c03c108080c8410f607400019481020301d40740c5c1c2c481407004c4241c0c800300c003250210708e040d43c0d1182c20f610814058038403562500007039104564811070b51140210381005d00c0303142600c0400162086050b041c0d01d464048030050442c1d034180711920058101034005c4000c4003a10b00465 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 837889784 1250 837888534 837888547
    0x30f03270306231302060c030912030904060b1204200423071d0d030e031e191a0a0f020a05092715030304170a0b07030204060e060f 58
    0x440c11207610546002d52204036004422204001c240c1d00392586000b0090207103448050f211242c5000b01d0001c0c0200400191801c032480c00740159540548001c2c10b0403a510001511f0b250703203400c41c10070188510307d4220000f4243c1d1500d42103614244903614601029540c81d15205030716a404040246c081c41610895486585d55110b440e0455032100c0c00c0701d1000c0b5080d0031190101c80300410420034401d81d40e180002424040107403010b00001224078500e11001407604407844142c00030040d0700340c8034082c41d0710840c2c0000d4406a803801c0c1e41030125059401e0030040101171040520300503120360f020700031400a40b0420b903802c552002c1a0000881d42540902e501e804907806112040000b4030049004c1807103103004443d003805200d855510300c0758002109003c014490018007030400c01d600c00910200300303450a10a5038020101c000f0041c0244000c50141911120f0b541f504880068800d00060103007030003482524180c0d80696214800900e0319000d200d02680004441120702e081401030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 837891034 1250 837889784 837889847
    0x18050a0b10080403030608210708070204050f04030224060d0201020c101809090503040b072603040b09010e06070e180c070201110114280e0c030d0801030f03 69
    0x4850a645140e03503006241c03070b050400404482c0705812201141e001000c0323031420300070090f6046811307031074001480c0d960350802d290444080c0b1442d07000941041c00c100c2003100c1601e4011245100b58004d4081ea45450701280e0103103407811450107505461a103500204026092035810010414810700458001c000c00c8070015241054418a1100150082c42d400d0440c002e03000c0080010126098140310071843c40d07680940320300403405101d04100b000318442090000d0395032004044414594402034a042c41ca4203464654404c07141503551a01500101d035140c2d00508c100c080d410f1440700905410346451408071400891080d002d07070711003a00081580c800b10b4000740540507119410100b0398403202c81c4005085203441489044060345002c60b20a04440100c0c1380640c1305020200b01039115840c0c0d400307180e13141422002d6402e254504115040d10b07140c00540203950002c110200d4010340300740b00c42103d15041c24080104402200100e000010307021720f20b28581402040c00e8000b2000400708c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 837892284 1250 837891034 837891049
    0x60904050a0c0e06090618010203070c0608010e0705190819050f04050c01140f030601110118020a141305090a140a020a0b030c03060f0a0906061e0918050a0b 69
    0x4a56000560700c80c0c034142d0064000c05180c2003420140c2d842410035090b1800900035001d1400d02c9001003107008800301d0168401c0c0200c40c20103912100040700d06407a940c000b8140c2800740a501c00501a16011401450240c825038000b0801801d0320f20711216452400c84071018050400c4130f00c1c840c442001c2c00307004024002d540c491412150740f0300c03041c50142090307450f101080c00c05c43c1c144208484138224040c1590301312141000d80d030642070b03a00c1d229540129414140c0c5c000c4000203501c0e042c80a61078440d44458002260b0003144c2c6c900c210758565a90003c400d0b00d41451641c445040a1b400025035a2038001d07a50060900003602c4107150592601ca000200c0040c0c0d040d181c0d08058501d40441c82c002c4450030281400c4107015095191a100c003001c3c920000d060340344640e80c0c40014008a80e50304c00400007904954005214580d641c00c0e0207032500c0501c220394806003000c191854a141e21400d0100215440365002d6044000440000070003030001909003001c1c00d4450100e20b0103502c5244 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 837893534 1250 837892284 837892291
    0x30c0112110720010807020d0324030501050a0c0504050d030c0c030c0602061b161401110d020d0608190813030f030804050f0f030f1c09080403120306050d1106090405 73
    0x115030381d1410b2500f1400160b079401d101c04080c18465858140860190300040f0520560494100020300845070748807030300701241c00ea10100c208042100017200308041904494050390b500c403000e101403250307081d00b074800f8091809540d070042c2d140304101300880c3c8201c4041500c03a01441140428070b881e511454181d6503642c1200c0090f0b4809401e002e460b00c803002c1e1240002d1101120507040004c010101c0f8402c010f21007014103015400e06c40d1100307201081d030050314541e4030300c201942d81c0c1c020200c0e510040c4d044010010145071901c074000030840008644591011461440e00008601560324882c040e00020350025200071b10580110004100100541d071103402921030710f41c2d0b0b15280c0b60840c0b1703045a0305513106580d0400da14072000104000240c031514101d6222464461f121403010052015240c40c1c0c00b0340075030500c3c8244d0b090100d0380300104240c074050341ca041a12000301d101982a202180f240b180c22110300d085100100d000d80005005011009000f1307840c02003030400040c155081903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 837894784 1250 837893534 837893543
    0x50306090d0519110712021503090c04021b15010f05011805060313060603030329010c082d0a081e010911090d060b0310091a13150212070e030c01121107 67
    0x46c14540552a00210b000c0742c1e0a101c030506440d500d41a017180361512600081140241d4022484a241d424003109190302c02640004443e10941100028681da140038440c1d10050b2000c0c042c0444c40b075101344205840743c10705c0007442c044c1c6403611040c05020740c00142280300134180e07001c0e0100002d016002c3c080042d80607542c0070031706240081d11a44810740290141d81c0004008840e001d80e41d170403000b20350b03030030340c006a43c60b403201b0950300c40741054034010185044c5100d201502e440304440ca640a04100c001b103542e10001a035410a102e807095072000d16041040b540d80e0010806407440e50090780b901c40c1d9540f40103080c0300303040b0049140000070f0b000844050381c07252001c5202d03040402c120040d13010002c200744062811754a50b0314580c041c1c5000d0b2130f449642c400002c0c142e000380c0008002c003160310a208041c503e0071409114000c0d0230002c001303455480440045180103201d503d980c2c00324100103004d481151030320070055a01c0c0e407100542010080c2c590148412001c00c0001921516000d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 837896034 1250 837894784 837894809
    0x1207080d02030c2b0f03020f0c011d03090a1205011d010c17070917150403021b0a030b130309080f0c0405090607080408250c050306090d05191107 64
    0x601040b8107103082505801203040070050201d110351340e1201d4070500b82c58a403d0500c2c00107a4403030100c01901c40d8200404625500040001d0794500c1580000311404060282e0503030f60002040503901c900c220800d42d82c0c001c640d19000d020b040404007a219060b8410800011100340b6884500354005151541203001d941d134504c0c0402031030700880b00607140c551001059006140c80300010308503a42c14000c240350303c241402c51440000c410010782d803101c180e000000c422841c0ca03240003941c0d100d0340a40d800070141542c2d04a602400c0c94018041a20351011000143d40d880b141c040701907105c0c491080c1d041181c000400241d4410501010300b56044031000752030302c401a90280b106079400503082c44102d600c8541002030a079030184d51140c109502044455459650618204802c5c200c00140280003803088920030401400025101c102c6400ba002d607030456031005c0300d550710398000040d1395021400411214645503600300410580901604000d0383c09628854094a010071030381000900c02003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 837897284 1250 837896034 837896047
    0x1c15060c030807090f090c0203040b0304050717120a110a021216060e03060610020a06111c02390f010e060619032d060f0b03010c020303061207080d0203 67
    0x9004010950041c90360800131030803464400310002c046a1407003000440c680c1e0340c8010450314030900c00c49000741480503820b5141d003481e0810503110240e511442820f030150048a00d80038901040350300304034020312207040c1040c081650980ba020000c0c4508021805851100d8005948117522854203400390b0f4001c10140d40d142e18050314030b802540042c014015190410003d0f503600181d03031070780a04162009044040c04250982c40c0c000c03c4800285414181284c8100310300e888400b078603040c00000d50002e031000ca00516030b001c82c400c00c401c054031a00c10440c2d562030107405124446502c8625004100d40300380c120001c034240091281a041d0994542580c00c001e850200078041d00908101c03400155200943c0f0400d4125483d4803005141804507204c601c40c114160b03840110f0454030203010543c1414601d0b20b400202401c10300c4020003441c04a108030281014030441c03448400640040d032450704c411080150180104041403464030900301c021030b002006002051100b50150011510f450 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 837898534 1250 837897284 837897287
    0x2030301090c1e0c0b0601050c0c060f1c02070501181505040c0b120906010f150f02010b0409060903081501140702130212010608060d080d1a0316031104020f1c15060c03 74
    0x417020300540e040040600510709142e00104418400000440f81c80c1c0c4d9880903400d0303000660040e4002c2000c0c1d0b00c803152a01c1c0c5003111980041011611a02c020005070280003000c86229001000140101b80726803080d2070041155880190030600030115414144c2e40c40b075041c015036111301d24450882042000780040d20b201000740740c0c05050182c0c0141b0005050200446108041004900820501400305802e0340e00030352003101c5810b0041d10a202504250401c02c0103401c80d80c00460004400131300080c280320f0001a40c00307041d07505a4807241c25490111240c020b940250034240d901440240343c112181007144001e041400000354580034541c507250002e0100c000042802d07000741c030704004141c001f4070100c0032502a03803144000062510300c4a800403004000101c10300d5010f06c14207452582e409061703180c140c116842002070140c48000802800180e01600e0714a14100105008410305c100a50564055010315400000b80c4400c0c008180001d400c0c40340d11040200e00800340f42018103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 837899784 1250 837898534 837898553
    0xc16150c0323070804030309020312030415052428030c0812250c0b0c07050102010905150429010e0106030203042102070b040312180602030301090c1e0c 67
    0xc00c00d00450ba200d80d501100145000340024004800c000f5072100050416009038012004039401a0881300150ba915804000d5a4010782c0c09484140191003c44840389d818003c180c818040300d000c180103030b84144450301c1a082d8410f101644854017801070443e0710b808048400021180c90221142c2c1c038034504100103861019048440c07950003265200d500c020301c050446010070240c11154440c904680e140c1101d010341c040e001031039500c42610015040d2819000b80a545e00c54205840380503a81d03200580c00c880020703c00a2154010071010721020f0701859220303510600480f50741d81510913201c10020000c00700c025440c00c0c0060040107102d10040b10040300c0c0500b0700ba080452a50507e901c5140c4150100302076030060441f600c85140a072803003400001c00900c00701503c079071901d460346440c00c600c18100720050009420a80b4203000c00000480c44000c58041da000366185900304019000075055000922051104200400c444000c400d488003905a040307950314a40b00006140c01c8502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 837901034 1250 837899784 837899801
    0x3071713290714070204021c0c11150702070f0602071415070b0402030f010207110301050c030c0f280f0305100503030906090f031509070f030305030c16150c03 70
    0x304849951840e000103a100d0803282c10801c141001001e0008084400640340f1910500075040342c00803840c1480d00482003a504ea010580b41e0050240a481d8201120703503000ba840a0380240c0d001800b60054203004805450304002940b064400c52030320b0381420811303030310795500c078000580c04041308011120b04902020705c0c1100c2140c03e400080c08101002d5581d018180010340004a5140400d04540c0c04021030700b00403007100c000f5500c40e6401e0802d0014120010f20881c025402c00000402c1403420384102d84c424508000701a00f44030031228610800e400000c603000911100304094690034034552003146001c00c040e5a214080710303070940010161640503003141c803582804842030060b554040291200810261101e0b41c94841150018040d241e1607040c0c150580102962243c0100c5d01507540d5100d0b4140381c045a0503141c0d038005046000b04140300c090005181400400c5d0704441c210000c00322500034083c01120440b043d1120b80404d0b0740341d0001035040c1d50f40d03d050007810360107000d003e03603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 837902284 1250 837901034 837901073
    0x10501181104050d08090a211104020f1c060e010e090d080106050912011107050a05190309122a050427020f01050720091807030803071713 61
    0x40919202c04510b40d000c9080004044001c0406c100e1000c0e11404c150000400102d014003030301d0740c0c080031141500180386006551205d42c000e2180769604040c0220303011100a00d1040f440d0000d2444c80030350803101501c0b803040164858100141615040d034405001c1d0803d055103071001c1c2000310510340740060480d148808c0c02410401080742030b130490181e0320000e501703031000900e0700c804910035401030a8003200401584404203407141448400102a0310952140040354510796403c11820380740d054100006002808803030051003070f4186410944c09441c814011420610101c580c03001483c956020b0410441c0e031090420881440c003400f0b0100340c1d014a0410b07210940d6003640e062811000ca61020b030145824901c01c4c5400d0340b04a0440d00010340090480352800c1510324a000311030f1041180c0b504c14030409000c240c1c3c1c0500f100d0303040206011135004100c4a032840c0e0f1408006c0d00018220800e200c280c003100c1e0740702d8007611a03683c401c180124001503644140c4c5170410195403503012815 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 837903534 1250 837902284 837902287
    0x10c080a1a04111204050d0905060f031906051206101401020a081b120d0b0108010509040f1401060e1e0907060c0501020d0906020307121a010518030105011811 70
    0x1040441c0d8100341800314205450201c1c0140e0307000711140491013001c0c007041c0c2c0c3c00c404104100a009022070100305140f00b99640503000395598041103658010915030700800d075410070204200c2d03801c505140f0305042c1e1000e40400c425644000240304e4654134034021550b500032600700201c03120a00305000c080c0c103e005001d03000e0480080002d640319200c0c6802001d90200040800d01065055110f4489021003011a41c81244000c40807805410041008102c64107011040000750300403614941641c402a020811550b0b40f5211694080d04003e41551848000030041d107481d0400e0141001030300000002c00400c0c00d00c0325503103100d9051001d46003010052442808540c07240415003a0884081d0b2411861603915424094024030644810080711490b00c07404a0030090180c0141d8400c03420b5455142040c420310300500c090303d0040d036042d540d0040720382040b011903004601a002100d84400c04003000702000021a084642c283c1114140b08062240009402d0081c01101981281c4d0384901c2e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 837904784 1250 837903534 837903551
    0x9090f1e0612020d02180108030a020c1f0507022d0306010503030a2f060a060509150906040c0905060706051b041203050c010f1a12070b0f03060d05060405010c080a 72
    0xc00101c07a42e0304000d00ca115804001010355985180e00010009019110350165030344041d034a03500d03805130f0104009401110a15803d61400d80020820319401e440103400019503a6400c07100e540c0100c000300e034000c00090840203800c0c0021a064010000315803840340343e06600040600d800b030142c0c0850300c654810802110001c1c0d2204040701540c24091a40c41d82c0e5101541c1481440314403903070440d103442103c0400101b160550051011500190780c1c141c01c9031a1140343d48071001c501c0c0340343c9802030804804150a420541d0040f2840d0a1510f00707084059107070700006c0c602e5401440c041d52000d0721402030110590704071501900d980301c20b5002038076191503c0e261100d9140c02d15005002d203d004074400c02010f40a4000340340707c03070007200e007008869403116819080d10032800c1464003604000c1c20445001354001358040603600420510f81c2455100381001c3c0f000d07480104025042014080003000152040148070f00951003a8000b00c3c1e104042000144004402055482c60f06c0c02c18040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 837906034 1250 837904784 837904799
    0x1801060b130902070309030f05010f06060e1807030b1305041101180605070809060a0f02070503160e07050f03070503010e0c1801080c1905090301060e0615090109090f1e06 75
    0x144412525090070141c0c84031485c0c281503035082e80d00d610140481d4085002c141c00c2003c10351018400041c41c143c100074554840740b04841d990300d5030fa01160441e03206500008580c4000048a0340030006107004100550b0680c0440c15203040c040308000415225418003081006c4025510301954080c680b00d00074200005403d1540e42d0305109031300900000107048000d02c12030710103c0c0c0109001820807503a80041c05001440c0c4200c102c00c840041c05031200110b403e04d40401c2e194642c0c0c081c188000c0300d040c180711394001d19500103000502404010031625007401404000755209000984603181c5a6151140c03c0f40c174190024409921003a08000340d403c29458031510b00301c0c030b04c030a1138103614070b80d14080e502e049442510101002e40680c23039840c0c0a10cd60101c001c10011200350000d10036a5558584405100004d44c1c0c00755011140c00348216156088802401c10480149066101c1954800080048442100356003035801d85a03040a03c401e40448001404161182010003605180254 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 837907284 1250 837906034 837906067
    0x1805010816180b0a0308030f0708060a272a0c03090e040c0f0f061107050102121c15050f031507050d09060e0a150903080105090711061801060b 63
    0x14182c10089030300085124000a0b074088041100003410f08000c03e07840e8100449680c104882803110108400700041040f40b003502c00c1345c090740001d084000c1a0f230a0980c0c41b900341c02c10f4856201c0407080c1c1c0c40018a03000140c02665000100c44c0b645a0503529074140d211000c40d24801000c06000340813130b001c1e0000741e12a84450807540d1504803120f19454500d440d0f9404441c035840411501c00c1c591000c688583d200c4800c004981c0b594560a521000400050f51a10f00d90f105040c01340e000010031200341c00010006000d06001d02080d031001a1880b0700440c00c40d140852110008200d1a8051041d41042d46e00d1801c900c03022401071480800003540c1c1c0b030780c03220b000780080200000407800d8404100c46411a03656694030510038413050041c06445540d40c10314003829a08840d50000540c4200b069104bc081d2041d056a550a40784c0c4c03e000a2044244011704180c042141640b0080815801445031601070710041c01206946034140b4543da080d02c1143c6c2003035040120820440003400503548 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 837908534 1250 837907284 837907289
    0x3040807030f05090d1103010c08091002030601020a0b0103111305161206030b011e1508041209030f050601060f02010b010509120c060706020702100302071211161805010816 76
    0x5001c507010300030402e0440b180e008100c019500803181810010401c140118056004881030f8000c00026815070740807954801d050b01c0d0910907400c42400d00b1a08019074000b981d0255043c012504d42040707507552000342030000d901c01e44810040c0c64801c0300702d140c9031201c4d1600d4640745400b4480750820004110525000342c100c4010f11884000a500b00b01c5903410034401150403080040943d81e40c0c0802c132801010101202040302c540a00100e400490001045050795280c0e582003080d5681d662420142c0c40d0f292040d20610072890400400034440d0703041a42c45d0741c400c43c042c04940d490000c02400700340c2482c91040659040024115503a644002901e00d03014080f94007240300c81c044418030b4246001002e86a8209800140070018004550000c1168910a4034000e41100301210120120300606100418459444007860303151441844d44011600c0c0200c04c0c0e44051208072419045000300390f01c04102c1030302442c015000c0c0f0320079105690051554002910140f806051034035030400c1e090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 837909784 1250 837908534 837908537
    0x10309120c02031905030301050f06070803070311040b0705010e01110a170c120708100603022a01060503191104061d040c0b0a05190e01120c020109020d06021e0304080703 75
    0x5010600a642c1d041102d642140c0210390074220180036801e01c00c0c0c91f58001d0107100d004203000f8030240c1007410420300301d400c110340000900d0300303546610340d08a02038800655003108614060002095150358200102245482240000f421a81079070329a42517403148044620001000d104103064550803168a4035408151740700c0c280a6503841070100310f0303406000b45510307a264400c400c101070240c22003003881c0203031462a00c2700811a5140d00031801c3e40b1411010520541070781a607801d040004450300c09403134501100201340151240c2c0403d01c5c002c9610003806106001b04041c0d028410b100d42d0300921150b061b1000d0090600b00f014400015580404000300e2449510014061054045841e0080c117100244580c0e282c0380104010165005484504040d8990482c4060340301c0c080c5054000040040c1c684018681809800340014229864480e0941d500c440203880140d450000c0b4121440c8074070300068980780713503490120051944003241e6440c1c0004200348000310700c0c00d40503079441780d900d13 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 837911034 1250 837909784 837909797
    0x11a0703020a080a08060a080304033c0b060a0f0e130201110a0b060a0b1206061308070314010608030f07060b01030b120718020f091528080601030912 66
    0x52038120300c0d19401c0e03000508103950120303045609a074802c46017806031004071903504201d505d41000640f40d108511000b850025003201c66204000c100d65421006d80800b0000c2d00c000414000b0501414401780782201c1d001c03080d4041001386c0c6060703054a0068012188100062402c00110540d0140050a40703403204840303008d060116807003008aa07081030100c1c819159407081910740840c2071034055034641c3c407880d0010004206048840c098440c554402c07500030100d13864140521035a5406164282850102c104010420802c20012a00114803174128903103001c0121603182c1c219282508091140d0304200b02c18084000e801041c0c0c0d1040fa08000006540c40d60b0a0041c0e008110005440e90041d05070401800a10b13404034002c0100d50b40d410080c0c40345001c800700034040713116480c5280d5442c00d050011982a081c80300780e1103403694403402c29502d401c2c020349540047c880b6040100b00d050b4003070711007107050f1640444065007007402070074240b01ea030307121381d454111007101d07005040c041200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 837912284 1250 837911034 837911047
    0xf030201120f11040602010b01080f042103150b210c070602032206020712020c0a0e0901062418030803061c080a0e09090705030627030a0806090f011a 66
    0x24503a0061510f02c0310007105542d901d80ea498082c0c064141d04031070501080070000090004540020694801c0e6405031480d14481c0301b044662840e81d204510300c404241e5242010303a2545d002031441800b44c00702c0304816032a5404000d14608901240f2003001c0c034403c403d818840300d80d00c0a0700f0303501ca2550040c0013689a98646c1007000d60b0703502d180d59090800381105104000d2141e00da00500006006070b50038031181d403000700c00b46e9442c04000c0b072050700321034030000070450000224101034201100400200302c036070780c60039082c00e102403d01e101d030782d5103101c015100000390b00058103d040751003248a0301000713495915003808600006000354050414005800b9400031050f180101f0b075a0b00648480d107680c4032080c0106201c5503200c3c02401116980049030344c445001820004440c4000c0061040e9581e045040ca580c40c03100c1000007802d00480c034078501058080c4054844030341650f440406615054040000c140b5014025084510903d03006002c110400b900140301742d002150320541e1110f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 837913534 1250 837912284 837912311
    0x1020a090b0c030c010c170603070303020606010f0c02180601260c0a0203090918010f02032e210c140d0231020a08070f020d140d0903030e06010f03020112 68
    0x300e5048203c01d45d510340707900001d520790800c40224104005030a81c82090b500d0300d00b41691120b8174003019001d41c0c088800650305601c01d00e201d100c518020b182010350348031103902182d101c03041614140147c00620b4200310381c0e940d000c6201031080f6a4850a0107403002d0b030321030901c015203024081d0040c40c00005408c0c0030190080003100c1a50034060042240c2d4541f9549203024030904442c000344950a054946440088a00940c0c0c000c1c8076130085070003c50a0a01201480b00d15048400055a132100b030000c2c000d8095642c0007a9000c80d10480f5078800ca81d0315080c1095820340d0000b0120620602003200991200300203001c4055065481090030b856954000700a9209100348000c034051820b66038152078900e80140840d6441c1382c481070459101c8200070b84001001c1c400140040e4416001c02041d01d20071604c1e00c80c03030011103080364544a004684001035462140302500400e4130390502d488240c00c1040443d004181c0a99502c00c400d0955000816a141c9807000500702c54807002603040c0c1c513 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 837914784 1250 837913534 837913537
    0x333131e1104060f140f0306090c01171302100e040204060c0539150309031314010906050c0f010e0a1502090607020d03120204090902090901020a090b0c03 68
    0x15008028601088840d140d150800491100d0440d2201e581d5144070714141020700a15090b91500d80c2003004490500b5031a80c0801049441154000700004110078184c4090021902620848001d0984071602e8030016017400c010601d0f0800c511496420890540034035070f07401c6140703903044540034141c00650380201c0e46088201e0483e0b0b4854070015000a50701c0c0c01241c4000348600c5082600e0026400e003003d8507241c50709402c0e51400d201c0c0182d64441d0001001c4a184564100905e1142d500d6951500701310b2581045031000e035036074800034020751010b0301b5074000d0000f01400c61840c0340c000c0c03402000070640c040c13900c660014020b011034494408181801100c2c0c46028040003000030b0301d007031113100380e40c0d1003805010b5850141e203014034206400035008540c0c000c500501140d10b806020340c2030020a140340203040c0c080100c44180d8902010302c900080000306001200854140c4490041040449001c0e0601615a20400c8282c0f1a00d41100d55182142d6582401d242c48404001105095 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 837916034 1250 837914784 837914821
    0x4090903090504110703030510051c05011b051b0105070f110106050612100e0714090d0f23150a18061506030513030c020f01050d1404020333 62
    0x40381c245020400c403060700d1380c050802503000c0d503000d00064841c024481034224007402810381010030501c00850348454400da801e4060701c50300000549100741600801407020780500d00d0001f44001172001e041e8900748240030554242400200454117000d071024150076410440d00c03092010489900a05d14829401070008040142090b903840907811031001013610202d45490311000c5c50080031680d8490703094204c0c40340c841038480c403000e0a00202d2001c0c040c0c02c07504001c0c1c1c2c060034410b40b00700000d8881001c11401071017000300c4140c044d031244c0210f0080c000c580d04018264000309505028501c0d40c60340030340040c20031000040c0365000d840c6013068203a1403603003d400f090070200c41100303400c007030320104040721f1080d6401c1042d0f0304c409100b0f030403c40d040c40003c0e0018021064041c0540380014151800d1601410041d140000d00702101b0140d40312480c0c0d980300481d0541c1033006504092142c0c0c84c030000010007200c1c2c10840c07410607003070603408540712058800c0e090380060b40448445010302d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 837917284 1250 837916034 837916039
    0xf08060f1507050f060406060807121b051018120809041d06090705030d08061008190c05090a0509011a0304050102120a091a0c0a05161a010303030e0a08040909030905 73
    0x184c2c9010000c20340d0340d40c0c00588007115400d1511380000f504e01c80105081d016101103032299000b640107511000c442000381c2d10714080354410700c40e0000e41656200b64040501b407050b21440444400401c42d40c030408465805510038501e00000c55000a2a020441e00340520889000480e415041048040783c568421400100d20607401484156070b00000d40c80102c0c0c0c02142103624942400230100c070032800a80310fa640098080b5500d6550030700800760340c0e0344088130550070041d43e800c00040d6029201140749400100d0360000c0c034010a07045c1202c00f4009000c0a0710070340442d500d07280210a411a0446003804050004130102d000c002c03080d0102c910305c1c1c40c0a0410b995900f480c100340170080400c08070403070717078500130340040602d06402c60303c528030691102e540b071810505052016100d9500088088050905540c0c03003a000640c841110001480101803401e4290304500c0c015045035031951b60100c00da80101c0c0310b0000202e418080361306071003540e4000b0030822802d140c141c0707044603203401255 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 837918534 1250 837917284 837917293
    0xd0f05041a06010e0f0409020f03070f030c0b0901050720040f0209121218030f1507090b0405090c07030c15051603020705121e0c0d0f08060f150705 65
    0x2489610355040322100d060040411460b1079100c01076a80c02003641c07249410a03406000843c1c10328103076000340180d900280044d015155582c00207800c280c282c1d00084024842d005041c0203010007220f100c400341c0042c00540e0f1400d1142c90000c0c00900400310010040300030218201c4800442e114040c902420241c014807510595001c5400030350402003001780265a480c0782803002040000302d4081d800d45441f4128600b244404503130521419807022990140314140c04880c0e0030801300204503684d000c0755031003071700ea042000c4e009003040f081d5405041c171104244801d0001e69030b241e105a800421301c11303404d0740d40c0380c481c41c056401b000d020b40c02500c07004265944140d000d031560051441400280041042d087d2a280290b00b280110b00019000c0c1c5d0019141c00451000000141403803028420903004210b944418800507600c040060702058008040070184180c000080c900f55122509001c000740c0740a201280311141a5002a8880c112100c1100020981741003141c0c2801d4200c400c1e43d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 837919784 1250 837918534 837918541
    0x606030412021c0f030c0509010e06030702011d03120c1c021b010911030c18010302060f07080406020f120c0d0305041103070e010e0606070503040905040206130815091f020d0f05 78
    0x151020700788444c80004a4206407001c0c0358503200d6000c50b28032480c140c50b204002ca803001f0500c4ac040c0c000824410966696125501e1410480c042c0c026031501c907a0025a130340d82c01c0841842010348040c114040300d0000303010102459080305048036503120041d00041e02c5101c609003403116090040601c0a0552900f240e01052054080141c04514020740403074002503038072405c3c05070205a446109404410300700c010f01c0145410002040c2e1003a591201504040c00d680ba544d1941c0d105030700050144c2d00040b0701154901041c07214111128040c04500d0800b101001695140e000403615501010b94500002e0300700024141f040442001c09400c594495449000b0341d940088280a0544840109000140145007410131a2070b603a5210024505280c5132040107009071001410880c0e120320284401e41ea04045140c01c8001040c58030300408071003c00c1002030b0084580030b000742e0f0868211190a0711030010480b03108080c040f0030280140e58030010007041c4018010b13100c000311501e0611090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 837921034 1250 837919784 837919787
    0x8190b0603040b2710050402130516030b010e060a0f180602100e070803091504050612192c0307080310061106060108010905090c22060e0606030412021c 67
    0x21030720940d00128a1840302c00c81c1031181c1c004c0c034079034020305070150b1212042240d004d8241e000290050b02c09810001408400007582096490481d82400088445c1021007529a454014038401d68020b00306403505807000300104003180300300148002402420340e901c0003180d11401c50244035450800b005000c503500c0b450000d4542d030002c04401425810048941d851010102c0c144040320361b20b1004620344042a400e020076000c0d000130302a040f903420721000800c0e4070f40c2002890a552100c20003030301882c0150010003040e20101e03004400c903141003114050505884411952045a01014110007480130b01d00307441c500c1740000040244101009020b90716414502040c00d03034009484440341d1580054090740c4d1500c0440d80c40703001030781c41c3c00100401c41c820b40c041d0f900300d019481a0380103003010602161200c80115103000780c01c0601500c0200c4040341d031050201130700c6005110300c0306040a03c009030040c0400340011300300b10000c421004000c0d00802002100031940c03500b070090102483c90 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 837922284 1250 837921034 837921053
    0x130060e120909060f180921041203080903130f05091e191d0604020907051903050a090204020307021608010b01050f09030703050a1103060a02090618060c12040f05060a08190b060304 80
    0x1448110203546081e204234851502d01035400f42e9040c4606100303141200e40b02114895005003e4a205001c200101720043d102180b030070b009001185140101c02d031504c018080c0c1c84034000d050208440024580c035145540c0484075942200070220807028441c1007407017003c014040512a10b0b0340d4418403031030414075140440e207540b1481c0212071426455440303000036103a80c4075513162481880e90321052540114040d42c00781e9040000307150000341680b510ba0100d0100d034015111035025038840076002440543d102c010001400c2e010000b4407883d0020000a000c0d4000c03552408021000402c1080c03070f42d241080100700464000044500c49942d9040614600101c0b501d050300034081d000020790342c10040d0085810b40e94000d0011460005842c88501445046000c4564401d004200516410804102d184002003444604c00d5450f403912841c40c801c007915070701607401243d01740301010040743c10000546c1d01481c240d009200300c107010310b100c1c401003100e6504103a10480210034031003408141c44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 837923534 1250 837922284 837922303
    0x180501140d080307030c0504090c0e040605010216030f02060f0403030f030e160b0d0f0c0504080c040506011b0c0902190314040b0130060e120909060f1809 68
    0x6015240600220a00101c008807800103000141c1c01c201045100348a82d11000b050322040c504241016120400c4a0580e000c13a84220001b0f108031001a06a160a01c80c203c0100001d000505070b1000010700884a8902440081d06240070748a1324015501d8003011030b90f14030243e4058a554940364507000d070500c006200940300091034a003040c60310282c0010042e01100c4096601c02d4800c1c40d0445041480d44004013140f100c503112070701c0010660a80c0600e204955003626040d4032541403045117440c01c031200a00b2481903040c0001d00c40107036000700b25820405041c000070609101c590a1a202c1204180c0c4800c8642e8070010b00d140e120010883d21243e103110540c0d042c0200421642030352001071055030042c0000d2401401044040c1006803000c101b07a005c610702c40d048407102c10740001c00a020000c1591019114407a03924048824002c00c0d8914007800c450a0a028945001ca00c08401c010325041c02503501c00c0120025540c0c1007280650a9280e800c8540d140c50443d04140e150042d4070b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 837924784 1250 837923534 837923549
    0x3021e190806092202120c12070b0a1407050f1b100f03020c01140906070807020d020604060c0c0209040309170a210c0803010303020715141c06180501 66
    0x15500d4401901c6049214003541c0d0003403501034240c84245080328501d0204049084031002070b41c1500041c0c0701c2d54010190160008058075013940c0900500425600b25064101580c002950034009035207d141541d90b410600c0c6032140480d40c0800c1600d039540328094002d401445404c03001580341c000010100803500d810802c0703002000d4401d0600c0007151102c810300020810000c244c5140c1c6221340d002d03103c484841000858610300c441702d002091036055881600b1a0000c13000c00801e10f0b00001c545030050a44d20041c510704208503c02500d881c03000c0c0c0024440b54542c00022906489941960101078004006046608191902501c40c91403031144205030790b03041c5180b00c801900403460f0010b0503002601c040c194044990400510303405640d40c04c09000704120000b0112340c000b00554041c52180d0001c0081c03038148000106c08010196102003040b50103d001c4000d0300d500c1083e075000c00069511101c2e010080641400942140d4114154610300100b80700f03042009504814100c030400e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 837926034 1250 837924784 837924817
    0x509130b01180302090a0f1d06150d020901031b1a09011106070905010c1401061707150903030f0e0907122f0304210c0605061909020a03021e 62
    0x8600c00c808001d4083c800079521070146000201c1d080104c0c2c000920340b000e1880c00082166211110409542e4940c0d52040c503540204100102004a0245407070390307403000c07103051402c200e20703900040442805020081064aa420070080e01c070060131005d201402140c401a07007124070180c180e0707500c0d4000d040c01d0b60014007412403a030318110700814118003401c5650394441c40e007400c00c0015201404510003c1721030206c10050584c081b4000e00c602e4001d008441c0c1515004814070100c2d900d4500d641d042207099032000c07c507030610690440f11400c2280c0e40750400146122121070b064078005141c4004c150010701043c20410141d030320101040b1500303462041005020142603400c070381c580ca000e1490041801403081c928009071010051035000348141c1c40f032000e031055403949c04035a0901038221000700306407900d44400c01003070740915a80984151001c00c1541122034220224000c02e204036032001d54005a1010080e1103070b0112203940c1a00012030404c21490564015180d004500105c2c41221 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 837927284 1250 837926034 837926057
    0x30e010e040e1908070507060e1305070c0b0903120408031006020f0a2a0e010e06030606010f050c0c030703050d080108060c1207052107110a0f060b010509130b01 71
    0x20709101c2d0220300c0e03520b02c00400820280925403001c2e8980603005640c0180140701d0200004e004201c0b0300013800d00c40d41d4168080d0100b00074400c8000c000c59466416038189000c01c840c0c1c40d0702003154554590003101400960315481030407400c40c070551400d009101d413404108800e00c00130340011805145070b16001501c3c643e0390f00c8100e841c0c07207001c01004096003201030003002040c0d00e045400140d00781302c1c12100c04040f201100102a6009a0103440402c81c80340040100030081141c40d580300d901a0050b0032286041c000091894000c1581841031090100d001d000c542010010045441c2c406411141510b840b428003d0b502c070060a006c4002880700380012600c0c007400b1a03d14010300c0665082d0742090408451041081001804e90040010500040e1401840070009004c3ca07040f01800740c5132810101c500904a07208070a0b0300c6440d03881051050002260720000c004415001000050300150580040310544a6840d04030f80c002110742600681d11295485402d40c4602621030841000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 837928534 1250 837927284 837927289
    0x90d0c092a03180b07031103090a02030c010509031f0f0c020a05060601020a02060a030903020c0d0f06240504020c0a050312150f10180803160203150603030a0f120207030e010e 77
    0xc501c0d07103c0c01e0801d21041803810000c0c40d400f841c140c100ca45820040b440328a0400c01403402d80007110180c1c141e5100152000650406000207030128000b81fa00e689000840804aa40c0303e48807210ac2001094004440007450070740c0c1e0014100384000e400038080c480f14000000c0d0f0714005180261500d00400d0f020504a600029003400c409601030302c1d09060104040055005250140003074080d8010b805c8040300c69500e10200f414940d12480042c403204120341007850849811040c0300c0204600c201c07440a002200c1c0030042c04540d011240136a54011488016080000b040402090f92002044031705848d1144480103200380720500d020b00003805008100244040d126420366084052088400c104d0380c4520150380079902c809408036040d503500c0354954510361240c0d01400440c040880303a00b0071880c0074804140915030305080c000c0d00b41880070019841c0c0c0300386980c0c003040c414801d5001c2c1f07442e4001c0c12407401009680e407085458289505000e80044103040e41580002c1200700c1d40c5141c0c1c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 837929784 1250 837928534 837928541
    0x301061409060301060f0317090d0308190506060f07080d02030a060513020415030b010c050a05011e1e090c1a0d06050d0c030209090f03180901080d05090d0c092a03 72
    0x300c1111b10005200703460342d160400c5115040d41140300c0e00c078040050b15002c0d01d0742030307080c001244603540b400c9240ca0110741203858030b12a9196940403504101c05d001840d0307501030549030a8120f91981c00e9450141e440c1c911784511810b454510f950340040104121040154800801c07201c041c0ca41c032032421a0240b215040703102c3da01030021092005002ca0a14034441d510110100c101810907055581068546500e484103014044503980c1d1213221600c106400c3c2c1e582003200d0314a072880be0000000d24800c03a100d049036070070202d003010f0361405000e05200c0d03c1c040500c0102942d510440200c1c0c141403060400341d11126191a02a043c007800007410700745000400400b940200c030340115107045a0030000c2004000c1c2c031090140c13054400301c40b1412000d2005200030126036000303a03035400903603061020042d0140c1c0090b1550b0042c4081d0702c1195003000460b0141181207402d1121178805107061648c038106500929106403400c0414422070500030190890294807040550500e44003840803402d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 837931034 1250 837929784 837929789
    0xa11301501120602031509180705010906080a020c1c0e030105130807060c09090f05040203060603060606042702040605092e1101020d021201060e0d0b07110c030106140906030106 78
    0x1041281407031140030440c541c1c003071600540c0782e40c40c002d200801b03000028a500303019188060080c1801003d03401c4c101d41007203103234010301c0203003004c20045e07250400113090468000c01040c0a65000100c3c04422041401010300d070400b88620b01014109001c0700030561540448118040c0d0302e0600411100f90740301030b004184130f03406288945400700540d09c00d00944490541b03c2c040c0140c403800400c280b00640950b020f03a0f00801c81c0040c442c509030040601d0700002501081c065000303142442031a4859004681c10740f01122100310000340380000707426200030920072001ca2280301140200d030340350313001d4024561000200e850f903058002e1010003c1603000f00c118003072448542d404983c0f40050240174090020082d40c1d00040c1061052001d040aa07840700c0000d110000350803005101d003681283c4242503025003590030456004156450380041c1c40b02400080078042c40c0d861448240800f00a0068025005070003480b20320380d9001e900203001841d08140e07200302d4940002135100c0c01c0500c2074504 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 837932284 1250 837931034 837931049
    0x170303061e03011514031911210703030c3c0c0306020403050703121409041d0f1c0513060c08070512030a0c08090a11301501 55
    0x318080c038a400588052540d6072500355481c1c910381c2c601c2e0f40d02e600c3d036030b8018004034188501414042d01018144000341c003190110701101c0c03422002140c20005100c01c40c0e0000c0c0c40001d000f40c050400b8800110f480d09164020303105e020350100405510800700c40f4414810711401482c0a02103020300d208041c4801c0120604c42098480150f8443d810000315903240104142098581c46c0c4d203c1006903030240c0c100340e41e254080c0f1010800c00c089d8140522045c58103191050b50b0605003281c49071244562032015100300c0d00c40c400c1112041081c0380340d680d070007840c50855075501040b40060307840d40a20110300d20b03003c2e64004c076003d000d40580111184142031410050445042030f0003034407074895000d808d5030b01910601440000810801c4010301450503840043d4072880e041e004101a00d20410005040007108030034011a502c00140345607455600014100811000c1d1020500c41050242c006290031141d9490a82c10904443d00030707000d400110a60355004000c01c03102c3c1c00070f0400c3c071400a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 837933534 1250 837932284 837932299
    0xf041d0a09020f1e030313060215040f020409030e040c0e0108060d0b0c0309070302060409140a0b03060402010806030f0709050f0603011e020c010212011d010f0807030f080c0601080717030306 84
    0xf503036203883c500300444402c2048842e0451000c101c04a46036800409842c250340400450030311101e5010400c0150312603542d21046141e203001ea98031000c04a402c030000340200e450f580b064080600800241c1305815020307004000b601c6042000502541c0100e51441c0030400410100d0b03800d0411500148204e50011000d19003919030042c1616517501c003d054002c0750242000c04070040c0c0d1130600510007403803505004640c110036505400c070131502c0901500301d61032030b06010103000c2c5c50111700c06a000c0c2c3c090134440c010b41d0320300c000b00e41054084001400c00d0700551b200461440310aa1285000b4207203800c45030119074030301042c582290070340c140401c8400d480b805810501407040d00188000701c0000000760500320785805191a100c1c0a8100d115101c41c09060b00d01c4a01700d40304c410380106506040b8160f424541502e4980b06d180c2800013810750b1107004000001c1c081d608044540210058080340c0081da0740b0300d031940e201d0206025400e0194518003c50300700c000000145c0f0b009903001032804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 837934784 1250 837933534 837933559
    0x60c08450423060a0e090d0905240703170c0703110f070e071103040f08060916061d0d0b0105011b02100e032103061008040c0b0c030f041d0a0902 64
    0x100c502d120050440340d20010711540454000100310029014412000c010f00841141c0724001c0c01c294180e4001d64015541149401c40c45040300c1d180c0e0012900f86c2400317641d01e040a00f422030366603030100c49122840001c0418480002282c03001081014001d030b58040c072000440c00915115203500c240c1505a501882e0700748400709500c0c4002c6d801c40b8150522054207a0401202411604950f11040103216040c004000e004000c0c00b420390b10086d031078058103401206503051340401400340551810803140304991003c951681d00813000000d8018000113060040d480c1c884c0203080c0034080d0354002000c20f40c440076100b80038000499999802841c0b4201001403500c1146c0180300d80c0010382c1d2600c540242c881107c0c180b54003601c0301001c1d89401a5407440c002d001d1040c2e07850705007040c800300503160040201141e0310300c2c9040c084d580003006445c0e84044440116146004425801c100d010000400003079000c000c02185041202d074051903070407a036817002e421049408503007002c1d40010064900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 837936034 1250 837934784 837934841
    0x1d09010b0904020f04033c0c0e1b1204030f0504081207030e1804020a05100806060f04210606090207030210090c120822060c084504 58
    0x41d061014044003068203180d52900c4807e00311001c80d0844a81d0520100700c40000d00840381c1d00d02d006405e510785100c01c403c2981d1038581814840c81010080c00030315011950150740e0007080074003240b1007826140c98024171500055070b03075002e480890104812a940c003980c079028078182c904484085018048e0010401d00c10f0100f54002e041c128100f00c0c03121240b0a4580d03800308048211044444d15410038a024814400d80b48000c1e007007a03220700c4919456000d42d0381c1c4003200130f51140040d00d019485121444a03601c0070300850f0804c4c02e0440b20b000c0084101d0202000e02180d8178017480d0140036103960303201088100d03c21000b0107030040c1c12052840d1050070706a0482d41c401c0b88a0544070340b2540d074542c0961a00703202501c0864841c1c500064080c0c40c20f208684025604c0b4088220849803840c1410140000c151558004e020150201760312012070b206910b0303e10100d0030030304881a0300e090011036074512041c015240d460200785085e401d203e81428403442c1039440f03900d0040074004081050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 837937284 1250 837936034 837936037
    0x1a0f01030c09090303090204051302090108011b110a080406020d02062503090f050d0201020a0e103c050d15061409030115031b15141b010c1d09010b090402 68
    0xf810b8041c5615036001c1d500584892142c42d01c0703204211403010315400c40d441044094881a4800b0307220380c2c11300102e030b840806d0144034462540882d0800e000ca005100c43ea441c1030000f1118040d0007a8804140000c0198020800208201c139950980d21155901d0001d1601044001d041c034400300041d0b0300c1280c40724002e0380b101c1c0b1070300d008034444021440c856a03401e2500f5541c1000c100180d4011810100b0160482d5648070b803520304130341d50b508020009600030851901c004d85a07407003542000340d0701c15201c42e16204a0380040814403461402c00d414401500c0c0394400110466100e00e0800b0100c511031340240c0c0c0354280e900c1c40d910300003c0c0165184803522070f0040c9140b030383d02d55a911813502a240703004800c0b00c000c0d445858040146c244007262503d00b503810f940402c03000211901900c41c92544488900e20b4003031495549501c41007000103450035401c0d0000c01c45042d6190040011400d9040a40031042003445501140e140c0c14036030034807006000a11980746298401d10180d84145450340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 837938534 1250 837937284 837937301
    0x809070608150f0a0f0609061b1106120a06030209010e04052508061611030f121005180f1605040302060c0a0f03180b0307050909060a121a0f01030c09 66
    0x104400e0030325800b82d0003d98943d426034043d01060306002010840507070400c0c0c0707c8004100f43c4c180307120130307120524402017000d009000060148006040000d85695a002a110391103540b0503903001d580782040805006061900042c2d105500c40c500000f00050211201c511982d880f01c082d154200180d0300c1c14880841251010b980300455800c003003102d070010420144100031a040301c11880000e210301810b40f1104401444441e0001c1046c01010322404c8120b420300100644240e009a82e02044820f001c10340e5004a42c0c0400c140c249100c102090b49025409260481070310900ea03110011040d89244001c11184027083d420b2000300058030307202024083c0c4129a03030075580c0a0308584e0b6078410b41030403071500710080364804030441c14440038610714401500d1555016880e41c01c0c000b40c064014040d0750041c2e885840d150001036080e84810341c3c954020b01e0117444a0314401c03480c0c504030048a40c03c9412515540b03980c00069400101c40c003040c0d0480340c00c260210001c0e070410003600d006e401d440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 837939784 1250 837938534 837938539
    0x5040804050411300c09130903031b030506010c0839011103060109180e010f0e010b09040c05060310080a200301090b0c180d05030a080907060815 64
    0x24403000845403240d000c2c40c1510190f0010090740e40c03c1e15604e003141e404209070b40d8069580640e459102a4200565250304032015415443c0c89041e0000080e4002d2240c000401c98117080c40000802c25815800c0308010a1084094141240c1960700880459104560203400205c00c2007101c0080b668500c010082e5181d01014150010156103040d880c2000070440009000403146014106d6a420312810030f8801813189083e1841c18620002880c981b00b034055003800701c081c0c3c501d80b814400c86900c030b00346d1315200b000284200303600340200b08010403000b403c8101c20f50800e040305d010740c90b0a0004a01c110b074442e480c080001d003090240074850308020300282da2012500d10104000904024403031845104611510b4091790200f41914904522000b00380680c0c10461080b0003d280c6d1801107174020511600b80d6100c0c11200b51042c44240c0c10420a50841c40c8120340d6024070401000404030b0070415150b83c0d08688803c0302c0d1a0380c4601901c6507000207200500882c221a13601c0094005a80d0300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 837941034 1250 837939784 837939787
    0x10309030215040c060f021614010302120a02031801060e16050409060e0402122d0a020901030b0a180302030d0218060309060103060b0307050a0e060312030c030f010e070210050408 79
    0x6181800d1805001035800b80d40c1000036031000c200c1d007980700d500406c03220450302c00f03840c81c0c1d15032224042c541e00481c000d110745920042c018983c02d03482581940c959065601d40c61680d4103117921000020b61081d1070380c04090008004540c43c20f4014000c030780481790344034603c00c125500c640c0d25203054141242c20f10304020b420400055202400d002d5140030f48014007038013003641040d00c1008400a010007c1100035084a105071000f009043c0c0a1800c0d950f00c9200d0405d9251000c86031030911840ea20020f50080980d4008418040003800462140a20020810404940051183c08c12a01e68130050060344104a060040c074096005131080805100440464807400300001e18540c000b202e11000c580d1000c3d004000b40010360041d28407520781070b0040d1038410309080100710031008500507400841110f401049080d1010803000010300069040d20307880e4140a081c0d010264001d45116603114004030000c92080c0010150a00032303d0141c00902c41e980c81600850040c00005105031f550030030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 837942284 1250 837941034 837941053
    0x1b060b03031305100305040209040f020301060b0c0703120c020919140a020307030501051504090e030c01021303110a0605070f060b060a1101110a1709010e030708040914060307050103090302 83
    0x400704060300803084803000c1840e01c01d00f004248524000c11880810070035060030248009600c0d01c2c0c0051750440c0d040695a02d004030a400840c0c00f421965000e848022000519000300d28404038403030090341c1c4500821000815803071000c8940d400e81c40380c040d5201c0d030303540f0100380c1c115031188030380011016510012405001c103500e0f81d80c103100102d5030104003030303000010002c0590b8103100c0e45000d007000300d81e001c07050140c584203208030b40114081d201c010b0342e41c3c00324000c3e200800c2042e5400110054001c0d0f588041403900701c1220740311803104580c202912072088285140106010090b1001613407a541040150346031030710200c549040554015603141131021040d140e10307005100c45090303620740b400b00d04040c0303a0150850b030580c1c0032001c1855043c0910500c05a00083c460fa80b4004010480155200c4c00007003401808100a404102d11002a0b03410411000c100500122084100200480034009402100d8580115182a0b260704907400520056000c6d070310000916010740f046840e00758 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 837943534 1250 837942284 837942289
    0x150f03090f01050c0301051c03080c07030c300905010e0d15060611070609080c10110a06090312020a14030c07020d0c03110607050d140f0304030906020c010507031b060b 74
    0x4400703440c0154074004c00401030149040484002c0088942d0030443c0030a8502601d0040211034058031180701c41c0f10004110f0b06240c801d00340703842d001c0d8018100b038100d0440721100c0c01c41c4041080040b80c030070b1008100b040c0b0361070150041c0001c440c8113854009c0c00c44911400c1240180c481c50048403030340100c82446c08404400c0c4aa20003504a80d2540b4641207460301805240c80303c503030302c40340400a41242c140720510010178050303d5180181d800060720f803142ca40030340341d4000e501904402441184009024460b054100144003402600c421404d0402c02a180e4180d03c500348841c40401c01d20303584084230003003082c0219403001c0005445030806405900198000400342805d89518024120038020700091442e1101901d4049a190f4500079241d6142602c0768640d801c0f21061040d070000c45810503050100303c900721542c1081c0c0384d60302e15091a02604003a114002c1200603c141010042c2a500840445803042d802d92201c0e420003003090103958020b400c070346c0c1c1203540a846000348a580d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 837944784 1250 837943534 837943541
    0x120f091b10120c0801060e0a180b1c0803041b0e130311160519051e01022b0f020d0c140a0f080a0806060306060403080d0b131a150f03090f01 62
    0x1068580d58041300c40d4507181c03005080a111140551050400c3c103810000b6541c150085e1810490300000422032603101c800003410041185018040440c00c03403040b008010540000303500ca244948110014a8110344100382c14904d01d0003034104041d00c05e00400d01144080da10400098864170384001e41c250034480540c104225034412034003030700909900380060b28101c081d0b211422a007885011030a071605000803500f01c0c00000c090f00ca48485088040c590340300740521003040020b00722080400d00a140c1656003e2060105000001d1180000800051000c1840c1400d20300c565034403c4580000d40ba41d02030320702c030310341d06003680d114902ca0080011552621409442c1c0240c0c040d80d1210030700100030300700e544002d0800d88201020410065290703200400d80c2c056a4202c06403d071200b213140907a50003062000315080d8400f2510403403402c40e4101d40c204000314512204102d1402c0420428003404108101c01d1490b040340501014200c80710b4400130f5907011312000c0c1101c290600521003242107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 837946034 1250 837944784 837944801
    0x504090609210809120a0f020304091a1309080306010f1106180d0302070c032004050c0c011808031515070302160b0c1005100803120f091b1012 63
    0x925600140145030705801a00c07060b0701c88a564060300340032045c0094124103101d003442c400d090050801d96000014820019030b0082c0c0050348040180a5112081480100c5003c100520900e40d0b0323562010f510040e80106041d00d548181b240d800c58036090015250b10707042481c414100300701c2d1544c0b0307207034110308107c01805200c4400c1c0c0e00d02010320f41c1104a0400c40c038094000d040c140100030840c00590040400320441e40c010f0608040100c10003207420419071034100d0107a03c141403170140000c2d031740d5100c014081505c80134020080d00c2c0090952807155121040040d14540082c030003c2ca15035000c204d0548103001c010510301e00c04101d501c607010590815441a00180c1c03000c883e9029001058194001034500c21802c0c1c1e00308102c440321150340e01d908000d140c03401030f100c20204040b0343d01a8800e0000e40189000c1d26282c100e50400c0181c50403049892181012004002c036441e540041856440800c145a24250454003041800b19508040c54000d0810860300341d152055160b034890f0540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 837947284 1250 837946034 837946073
    0x2303010b0702030c01111c09232701090504140d09092d0c0513090f140402031e0c090103050105060111010c0e0f0402090604030b1807030206040504090609 68
    0x300d480e0180107051038000414401d50601600c21484d100c10306000071818444a402c00c00d503200d541f0410300803200e40d5200e0b84180703000d2000799a202c805c01c03810144800103c0d0261807010200c012401196141000040c0900020103000014091060240c20080d4018003d040302c1070417030044186103141c004000f180100140c2010070520200c01c03580034001007020b107008001e25a0560600303400103c0c114513a80051559034071145104540918291044d264600c84a0501541e56900e020090701d04103903a11308c0c25152240b02080d02850319041e034081c9401400506845800c04294808241c581244140c280b00380c0560301c1c0180d5900320b00c14040c6100740004209400c04200161400070b054216010507410102000c0c00181d108a6402140d44200c500c0c0b95111564008140240710305003401c0d4100400041c003000703102d01d07080d90328080c21031400314215112100308103d4498030a400700a610031800c0104003d980b0382500203d5203d401901e0000e500c1c80c081d91000440002140703000d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 837948534 1250 837947284 837947287
    0x27020a0b0a080f090109031403090708030f070606150e0111010b0d060b100c0519080702190f08070b09060a05090d14010e190803090f0d0309021f020a032303010b 71
    0x10f41e401110307000540000300031000b4008840e02d96005404100d0342810003031a6200071000500c030348010040d81005180d0340081e0303540c9840d000f141541c994858002a913066040071800618810803011001408031a696401e0307940c22031100440b5111070f03109c022069992036580c41c550743d41c0c8410f07a0451042c4900e100088031a00142800300c4d184a145408003800b5080c604200810030204100d5048480800d0a0680143c0380c50b040c50140a10440650408058611504e183c1c1d083d0b001c01050385c00f005501c90084e6a500c8846a58400c00e0203003190020050bc042115810030134003403d85008141003190904400c80d000c16541541a5421380b40c08524641c02c6410307810a200380410b000d000c201502e48501c281141e5405407500e0b03a4010000a4004009000b4003400c0c4681082000e1090a0395000510070f1402405406000c200303030b20944503d00c140c481000d850f4200202200160080c21026a042d2826101da60a507030a201320008015103c100c018802d1000354080d141890006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 837949640 1106 837948534 837948541
    0x1803090b130806040c080c0607030c032010060303030c0302040e01230a09060608010b1804090507121a060d0506190605120a03110127020a0b0a08 64
    0x10b0006020b0502884108141c030b9583c2811181c01c0c9044400d003550310010042a442094001404070f000f0f4840c2c400001e005103103c1d840120b143d00c1c54512058105122070815141c0c40b5060b010b19994601032007055014420788410701d41e2440d085050604003003940c00050410b000745489800943c3c41040344000310048118000f501805014100c3c0d590342e0240054842f40c06a1800b00308014004582d06078800e060300c510813080032146164004007420b120017400070340700c161114010b0002c0800c5114030450403000051185078407941019460386250010724010b0030541c805c0c2d904816440126400080c05500f01c110f25464100f41c00c14809240020203d50b48540d4000c0850701c51130714101004908a014075029032145011881100f80b01822a00c10140420280104249008070304201060b81d098143c400342585125645030306d103030760321034000d480828006040032040 = true := by decide +kernel

theorem cover : BRFrame.Cov 837769784 837949640 := by
  have h0 := BRFrame.cov_init 837769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 837769784 ≤ n) (h2 : n < 837949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
