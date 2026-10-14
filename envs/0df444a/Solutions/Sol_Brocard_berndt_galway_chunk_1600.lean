-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1600
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:47:46.100075+00:00
-- url     : https://prove2.me/submissions/8c503485-2b7d-4829-a586-d0ab7f1e5f6f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 287589928 ≤ n < 287769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 287591178 1250 287589928 287589959
    0xf140304061e031d0d02070e0721020702061303060f02090a03020409020102100f0c0914010504120f05030a0906120b1e03010603081b1b03070306020304020303120a050a0e012307090f09090c 83
    0x9a80c0d42c11410300c4d28ad900180c4102600e254401180c00300302c00405230703403001c3c094014044010020301c2c41a1551604004850001c03940c40845030040c840d0780b40035502c4046001c2280e0301582c002c0380718803d13440100d00780340d0350f07240c0b5841d024903194603e0441d145990049903102c019480c1c05058030780303401064188400207041c0c1c60001b00200020300c5a40c040c01d0784100341e0307440344062406401403076450b40d0543d0001520040080d0404904015a070f074800c04020800e00c03541d208001c040e44038400b048114011600e6680d0a654130840304c1c03c9500d00351710420095411071038454448807603140c1001040317840801d140f10340c49a4485030030040001620084c424400030001c0c00000c0ca990b4603500070303400040c01640e25000900c900e80d42c50300c0c080004d80c4503646400b00010f4914010601c1411100103403400e0466038901080014401c1c0c507a03413440c0c0c5204001e1a098001d0b03981c200c081700c01d003280d6000380c04030001d030b0303000007803a12603e0f00600000c501c68541000001d44403c49000902e00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 287592428 1250 287591178 287591191
    0x210f050d141207051308030a05131e05041e1514010f050904050a091203060e01090e031c0603020a06020c0301051b090f04020c0a0f140304061e031d0d02070e 69
    0x110030100f00c0c0310340101d0042c250504a0700700b0019440e076958103541950070000c2c1070b0380420400544c07241711a00d1500c2c690050508c1d8004c58551452070781a030540c0c030500c0d02600d80110368440c01c0c078180113040f9030004141c2e02444000d00410b03244030605d0300f4107900d5105082008036001c5c414140380d0b010b50320740142e440b0305a6809003041c0c803405c200709c0640005440b00c4500c59580982d030020030075005440152070000c1d200072030101d1800c4c03450010448140e02208245140c411b1419405001000301d908161408e080d4920074960320f14031400070603031607000a41c440d000400010b07250740c0100d918114442d04a00800941e034541e14502c4c0d030b440c100c0c0002c6a04074010007045a1924040108030740c00c0802810040c1890038201c01603142000c40c0c0c40541d500f12121031420704019824684e081c000047d040550b06042c5005805488030400040e180308404001c40e14600c2e09100703606c0700071a0030310151900307010503548183d13940b0307000c0c607012403001030040d444041160400200c00790701454 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 287593678 1250 287592428 287592457
    0x1f0b12030a12110f0706021b030a09050d02040f02040e040506090724110105150316060503010308030a020c1002091306030503030105010c050c04050907060219020901210f050d14 78
    0x15442206402090040c8070402c400d0401c0c4030724040d40000380007501d1700b540f10340e20050b500c0000d5018500e0f5080c1140000300107901c10460110040d1780103a4060480305c0998000030000d00902c001409000301182c00c60725a48080360000c0c1101c030080f80c26009600070f0007070f5159511031045054071010140180c16000c00d1704844280d50340441c103125100810146032104100403522149802c0d1201500c2410b01410070700740141c01460107011200441c51024400c00701d41d0329001000d1f0050105100207000010003100144207449590100c42c04058450151007450384072134820740094101203502409a01030010222801c0032a105000071f9070b40000040d415607207010f004461103922443e0031101c60003100100344041e1a20300a40b405144a00c02403e2031606001009140840d0030060b07105501700b102c094800b513151072000605440c2214060540d8480325000b603c040b01d01004021300c0401e4904c042c1c018842d000c9040060b00030242d80304181c1001d4002c40b25054010781c0c6001e00c400b07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 287594928 1250 287593678 287593697
    0x150b160201261825060215090607140d090b01060305060402090f1c17030108010e061006031104031e020301180515040f05030409060305060a18060902031f0b12030a 72
    0x3000300800e0540d10320000f0110713a03100c200c0e070341d5120400b458089050001100c4890900c2281e4040c40544d94034420381d411140c40c2d1030585061b23981c031600a46604284102c021001c60460282e4040b903603442c114250502076400c02d480c3c00100e8200034403901001900c7c0502160aa151034001c440c10b80d0b50043c819a1204402d8003044200f140410f170460000100d242c40d140040d04200041e100744100c003012584961401009a080d05e00910f103003e0907401810801c00410514544c3d00282d800078500017449490461203502d0768030a03038101410748401204068441000e0340c603000030b4207100340c000703021f6070200314400c4050f8001e41301e00070000c3e00300c03000f40d4014841258200307034401d00500c0380c28104100c07611800d0841e0301941089114640b42c0200340140401082000d030000d007490b900f04812000160070f065800340c07401d00207200c01c0d00c0e8010b9005560b420000e00401303640517180c042101240e82500001402004145c9028144034404400c2e0840040180c0e2283c09140d1100c0002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 287596178 1250 287594928 287594941
    0x10b041802042306041503020910020703031d01020a0b13020a08060106091802160803150f061c0e10140916030813030609060f05090718150b16020126 66
    0xd560411043c0d83c005005100000303020585c180d040100c1d20311a200141d550400100740001c4041007201e020a55100f0081000003952200d80e2038031038021100c10704014844c400040b801c0c500d00c60f0018100004c02020b014240e03051a4113545818400c07542030483c59960385000d03859035024410907001c101000400c001d5000100c00c0582e814801c06001450500001c40041c0b800c3c141540649411801108008078220b040b8001410010f0840741503600304030800010b10b0f41c1c400d40410000b448115010030307000414076080003424030f50034026183c04000070f001d2140101010b03241c03182c901c4c00c4000490310300d40010844080400f8680701c201030050840e10f460016278052030446006000000c0000042456071080151540c49880080ba1a004000d410000d484020305081080c2e00160020030110300180d03440c80c1454080c100c0480c01a00c85c03921044903100d50f031321004048a00244100c041c49004017003240d024400d032201560700807041d0400450599911040c0b40c0c1d20911008183d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 287597428 1250 287596178 287596229
    0x20105070210200c010926030a021c0516090603050105130c09151e0806030a03120b03030706020a1e0c060f111201050f01050708070219050306010b04180204 69
    0x520031243c44500ca890f03100700b01d4000c2d0303022200030b030042e0b5034503a0190100092010000b208a42107400003910421041e0451040d100c00b03031080392140e40c009030143ca6a1281442205c503c440030000b0407030b13898041ca001c410b4503014080480003402440b8045031250003840707001d0580e60b004c2d02c0d10b28102e0110046100400365208410b00b8017029200002c1d5121a20707174082c0550700c465076000d1104030010480190317480e41c84000410701804004020700c5d070300c0c00201e8410041d094504a007092100074043da0041441c0d15500c0d4041c000010094140710594008107800042039035200c907842c0b0400e00905e20b0030b04403100c250004607428014030105055420000c40d0702d215050005807020341ca07034014142d5200f0541110446218401007000c0e2600c00749640040e0340c04e0811515020b070300e41d1108000e204490000740b140010110720081c0c0c2142c00d1048000d06006001c5036007a5849a56a600d80e42041c410003889007484a402801134059001350703012540442c07140003000126400f50701 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 287598678 1250 287597428 287597441
    0x601050f0a080727020306031f1b05090a050a270b1e0f090601051b0a05010203090f01051b04060f0e060f07020a090911060d02070503040f15020105070210 68
    0x154000500100890b40003030a01c2090001c002155089034050740c0f84104509100034103290340500c51050080145a4a000c15840c8000d6200f802040c010010561203400a01e5541000600205822503603075002d900280101021101155000f09590ba40c800300310340c9131242c1c046c00c801c42c4d000914a00281c0030850000c01d00400c012004a052600b10000c00c0d2a803c64228156258402844003000383c20b05c400c00100c0490306441c940e0161400c200060098441c1c150b041145262400c0e41c801070321400d200e042e2078035a12000a55803400c00800c0580d035180402840c00b540d520b0080840c005181c030b030031011880c068200041c0d0829103040c005a031a82042c030382813401e200e02075203141c00d117998600042030095840c070303c500d440da80345005200d02d000c19a0401100b1614101c502400b10714207031811500740c8003c48503640c0e00c0421044102c00390203404d800400c00e00c0b01050108401261001000584104400031503440c803000200706d00380d4406854460140c0c201003110104000b00b40c1000d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 287599928 1250 287598678 287598709
    0x1201050c071b0e0f0609161b021302030c19021902060307210e10090503040506031003140102041409040b06010f0e0607080d060b0c03031306060510030b040b01030c02060105 76
    0x4000d50703984949003010f84222207028211070300c542080700910b0640b09003034220b0440381d030b10540c182d11a08081d1400303020000010004c01040e08038411540d500c2440c1c0001e04a8040c10342d140d0510f0b043e055600d400c181801c441015814110340c80140c800244110001768001c4200d09c071f450a41c0a001d105d50001d06044100202280d6503401c48140614a0f04040e02c2007000146a10f1040030701400c00c421501c011722280d05004070300b404541c000080d03600351402100c100d552074983d80e00c034030441c580320b5100500040c1e0a0000004480066018008888000894010b42001c1000308419108112001058010141c2c0820815480b4000030108201c190030103802d007804a10010b00300f074100540403594590009038090001105006240061034003c5d50b03242411b44034196280c0b24000140034507454140b40044d0014024a60080360003000c01a00071a005100600c0007009800d4081e18240a24145040c50095510a2003a51103076106580580130603401d103001c00c002c070203101c000e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 287601178 1250 287599928 287599973
    0x1106071b0209041b05221a030f0a0b010608060105031f210203010605011b0b0c09100201050a050c031b0c030c0303160806030a1104020c070306020c0304051201050c07 73
    0x4040162a2010400e0041c0c1c004c005800b07088070000c480620101d940e03007006001b001e010326495802102c0b8116010788003c404004500d1900c0b81c100103104030401c1814a40c1031084140108010324081450784a031030040541c1000d076a2111401c0d504141c4c1a540d50303000841c1040000d0f642d40e0a04142c11301800d2041c09000e1103662881943d1081c3e403c1280c002c003030071503400420118902445032000030002800d0408921a480d4545400914010b0014007000315601c00030715140e5084080390f4800300000d05183c10241c944030000c3c000d00040710717458440b0340703030002181c508045c000c192071192294201480c850074100059054a4018030b440d010a88800c1c010346160300c2051010f1481a240c424180c104441010402000404083e0a580c040c0d007000311040c012510900c42c516421606035005a41d80710104029407070004c0640c0050011480803441400220011009004441c000c4034180403280310510024200d9000703545a85c620201000ba050001d8000e1200b00798000e02d0000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 287602428 1250 287601178 287601227
    0x118080c011505090402060903011b11060f0411061803060117010f0b150c030d3e090d0201051201030b01050a0501031829090d11010b0102060f090703060e061006110607 74
    0x1125080d010001082f203020604041c41064002d1041010981c403684446408605003000e07204c140c5090403080361503000b01d8000440d2045200e403150180000031018044580c5903940f00e6103031101c0412014801101e500303100c40600b104a80303000741d1512400041c4084c0345400340510720174060f481003180b20501e0105012940c945010b900c00c950720b211802981d8000c2205145054030107402d032030740320b410321000401e07041c204010400543e20103030b03415540304080c080540010383d0340d4010b43e44401384601c0b015002104221764005003504903501136500d10386080c0c8074801501661802050444512103020001001c170b6480e50407088694001d42c0c680112404902c05030b02d81c41c0007290f028446034410321600c1d0581d0780c01807001e484180410020800086000c0000391070780340103000c0350780da644220003240a807401405100011079208800700100700030340045035203940080303507a4110a6041303800014024010048003c0c40e40c0c0ca20040c1c03040e603039508010b440c802540c00200e400b4440144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 287603678 1250 287602428 287602451
    0x9021807200709180203011b0c02040c09080d02010905060c0909041104092a061b031211040906050a0e01080d032a05280f0804050118080c01150509040206090301 71
    0x800d00d0713030312080c00d8681c03002100180141400c0d680c10000300003405240c0d12480e103079954010314a00519504507400b164000340c0a908580c100d105422014280c042c2a031105082501584021301851281c429507040c1e40da03034082a07007070b40105500d440c3c102480704005000160018280200200010300004907038216444403150710341c0030710850500861001c0075030800c00c046070f4000001c102c01e01e85100c80c1c08682200030000c0f004030b0401014010000480801d407181c640040107448541020306d5115030fa00d102f503501030708462082c0c50240c210b20038041046605142c0b8035050300e410750014082c100844104a0080c82c81c0d000c140d844802050780060f4445070000d88101040761035640c01e89070501e1928000144c09001d03405008540545000102190003044500c6100c0305810a50003d6407503041c0b030303409808132071044214810b911250a00b08210000a071528009031030003003100000d0303150000015081c41c0500d960091950000500500d030110041a00c0c0c0307806000414580300310b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 287604928 1250 287603678 287603681
    0x3090b07020714120118050615030601030c050d0c09050c09010e03010506030303070c031803150e0109150903140a05030f0a0510052211042315090d1509021807200709 73
    0xc440031541c0341c10550520270390304211071070b0190b10101180075080c1545150b941c90702c000f8862041034042da40c0561000c0031310040013008401808440340c02e00c00b500e0121085a1b003503104c09882408100d2044001c81542014401d40b8403c5801030015450f580301e5400a079440d03c075050341181000b108200d10640482c2844541006512400184100910680d4640d0940e0b20f070a8115105a24088820002c43e41012019250b170549800010b042c032441e08044800c4140d12540201c150310006803a11043d9002c8010b5109039982d03070303560105446d03c0c41c902054403016901a14400008281031200d4509501049284603550070360a400c2c0c41091380d03110660b00040485070310144c002c6400c000162180c414440408280070b481600d8003c440002824506c242c0c640c40d48030203020612180a46502810105940d005000f440d4602416012500900400001207004190820300c540a00200c00c407017500075002038072150300b40140d421881b041c241c0c80c065414214030406400088401c0107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 287606178 1250 287604928 287604971
    0x6030612080c0a08181804020102060412020f03040b03100e0c030406021c05040606080706050c060c2d03040201031811040b0136080f030a0311040f0603090b070207141201 75
    0x101611514068005c2041284400820340d202c244480c201d0308000041c0e07404552264816444424204042c5c0030100803460107100c843e04607000e20000030041807a105d500059445004c0e0480c040c0b500c1a00ca038810010307840180c1c1c90700d1480c8024008100050003075000ba00b803464a540310703843c9442c0c00e04c00a40581e142070740c064641996400d070600c11005c2c14000d54015041d14208a0b01d0180301940d0590790b14001000c030420300c0701c007040903081d14200840320281098240c8230042400220101840079900070f0300c6c02c0380400d150800c05500002802d590030130803500103070100c500c080c2000a010140501d42c806178100001c030380503100d4040b100503000e484451551117a039000c0101c0d40b2002541c0307a06410460040d806a009200004000411584044202c1c5030114022050241c1380c2c00324001c80d00921691a0300c41c402150040d410360107030344a40c0c0070358015103894542400990310381d0020302440b2000d8600e0244551a0304040701c0c04842098180d0001440b11015107100071740500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 287607428 1250 287606178 287606197
    0xf112a03060609070c02010804080405180901270f031e030902031b0a2c070c03021b2b0b04030e0306160e0d03020f0f030c0706030612080c0a08 63
    0x292100464a64201000a10352080b0140c030071244900b0100d1001e0480340714010000d04204d05400054100035100c0180c400803c03010b4030348400c070a1144444100b05108880c6101d1135840c080141c420000c0c0c100c50159035071100c0d000a9455409611840b15100f00140c00f502442052900300c80d40034400c8680404030205a03800060f88001481058280850094400034120900000364100c1d6145000402210030449503055040006420300310128183e499200c401b1054108101c072840e007105080980c41d00c03135401e4481d8030f003540342c10115110300c4020440d004001728481417000e007500d000c8020314a07207486a44c80c1284c07041ea2402c2c0c6800b0700700c4044000030209070311507085040c10004241c0000c0b450003070342504e10303401900030b00f80800f210007207106002078003025040c0f50080c081c880ca00c03251310044d92a8000c1c0c2141c8240d80c3d900841c511401c600c50700c071000904610078412203042c0c8521107102e2500000c0d54482c00b41c0e6070030400c0714071075500810300040001022031000703055854 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 287608678 1250 287607428 287607493
    0x316080106060f0e03030901080601020a0f0308060a08161503020702150706050c0f030c0a0507050f1e010b0603160315060309050111070812070e030304030303050907080307030f11 79
    0x38145030b4002e00c00140d00409000340141040b4940003544e02006030b88072118280b070254440d60358040102d00e17004c040000a0181c00c404040b00003031541c0f01d10f1240c82408242d40c1c5000d1182e070b416440d0b9035180c0420781c1035010350f40c2c000d00b17100c03600500108621ba108075203005418941e40b60005800c200651504405480e0002041d0381082aa400b03007591000701051210705184000d80f1483d0390b80f00c02462a4900000001c11000190080d020348101940080864901507610b644103507454441400a485014048019098914050065591000001d0100d0f030070340c0c030784d2544130042c00c10000c00b80081c10b40b02c0000140a2030044905002000103550104c0c0c040c19904200e82103a104040310116001700300562400304815808440d020440f070600c0400d02d90303071450103d414480c0702d001c061741030100080010625503d504103600844c4c041041d41c20150303907541556524855800300901044100e00309185e4140110003500b04809080c0a5810070107094003800c201c070440118403408803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 287609928 1250 287608678 287608691
    0x61d03041d06041e090201051b01050f0c090109120c08030f0a09060804030503060d02040608061602010f0902100c111f030509070b09060c07051c03260a0b03160801 72
    0x180c0701c046034190800d00075903041001000c3d5291491429480080e450b0000d80c0b148034540c11079100b1401c40f000340034075601502059a403440a21b018000544405030001406c10114130b100090908660020405071294040c051508000301000314902c107050b80d03440c007072500c00102d843d024030007003101040c1810800da64542d90030000e89041030300e0b0025010068000c04000004e0f800c40c080305c1d0088000c8581b0111151140f00160213080aa0010021030003000280544007142c4882d5400a040d01d4000307101e10300d0564000703c125102800702940c45060030440c0e403c514000c001e08406039004c3e81202c006134501c1c0c0b0210304005ea07201248100307800d5806d0a24880e82d4144500ea80100c442c07009425528038040740060180100c0711040d11503100010760760803500c4200000d4005100113090005102184403000c0c0c00d03103841e2a0150042428a11140c40d0345002000000300c03040340c450280340d15120b150002d001006070400842d0540700b1070350840701c1311100301c0f8404001e200000010846 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 287611178 1250 287609928 287609969
    0x13030308180601060e0103050612010c1d062503120e0d03060b0a080402101223090a030c0b040c0b0c1b0103150b0d06120b01080c0d020d061d0304 64
    0x4401007964422600311800500443d42d010104050b20642480c0128030b40d103804000500705102860341da960b070341c68100c4101c82c1e160400040345003204031074103640700200c1c007009002d03540c0324080400d0042080c030395210b0204403480491400c03060184c5000d0581c1143c09000710100c0d00c54013143d03065540291990000313558103000b49800303000785401da0f42c00c0001500018112500141000384280e80c85a541c00f042445808030000d0b0141c2500244940c24880002c05074407400000c1c00002a80e00b40002482d0f03050000d200609641e00d950390750240300698030b03006200040540220b0780280200c40005d00161000b002c3c2118040d950302a0812000c1c07000c02d21007480c0105160390525081031100300b030448180100d00e045030440484c55554844440c00f890040c041c0c1c0c3c02003150486001c040c01c0501001020107410384e800d80045279040d84940c0b0400201d1000d80000950040701c45d0800c01c009a00364002011075180400c5210510707441c444647d0864005410410001c0420842400d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 287612428 1250 287611178 287611201
    0x20f0d0504021516030c050f1614190e0c0712050a030b0a051302071506030c0e0601021204030f11061803060c03041703090a0501020a08010312180501031113030308 72
    0x52041620f6800c81c0f810703100c0c02d559503040c581d41c14054180321202d83c41c50188103042c4981d1034086000803d460f860510101c0c00310705038405000d00059211150707aa43d40d09e04200c95244414042c40d034031110864546010b00c0c0d44040c00400b14480c002044c040c04001609440f00500c0c0904161680364075141b4404000301182c500c20880e500c42e48084000300b01070785078251007070f039405200c070001b5a0300c0c54076050024089410031a8210740074a00b000010038400c0289000c003d0340c60b10502802c00e45c44a400480c1d903040c1c54010080c04410070481080043e070a004041030940c0b06a01c8405900850000200c407a040400300c410310400a6000040620b03060000680c012601840d15083d4201501c80070080d1030000c10740041418008081850501e04002c012070350f540c400000d540d520302c01c0c50001e0880b5000c1c0300c201e4541c801c031a00300c80c18a00910040340c4461101d042001003030315080046003d000e8500c40003611782c50804ca03030741c2c8070800c1e0b0603038002543c000d031101805818a601c5400c07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 287613678 1250 287612428 287612449
    0x31d0411030a0207031b0302032a0303010b0705150a0b211b0d12180506340f060b0a12080301290a1701050d0305070f0303020f0d050402 60
    0x5104614210321905821055001d0366045800726200684070605841c0a8502c000c0310310101c00740b4102e1504010825600200520100c40d144a0049060107118224900d004030a0407900141d001400144a2a41008041c201c1e00f4007450441c2d8600019161040c0d558805489041805850740842001810409581c0405e0014800d0260300788160503411520303010780201c01c0303180580b50340d00c80f001c075543c5c0400c1d0849240c00210b01d8900c404103010140840c2c0400d21101908170103164002018907242007079401c1286101032405488403012000f00452104542c406002c5c91040150004038030342426038205244182000105075802c102003205488059010440c28030a091000c4001900c0d101a43d045448454030300c49442060700d00103c1c400c4001680c00140301004c44d01d002901d074484828040c010916030350080b140d0702c82041c40420b00e0603a1024000c1842007091400091070504039240c803034041e150040c100000c2a80d007002070790050280d001003948803c140030661501c07100c20b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 287614928 1250 287613678 287613737
    0xc080a1e05130e09010e0d020a0218010503100507050d0c0c110301020f0711010e130507090f061403060f150a1706090a0e0a0b100e0108070602030f0a0302040b0703 72
    0x100d05020280e0642c03a02c2a280e4000e900072510b07404086081900250886030700e151400c1c05841c0480100c5d1002550b03020101030603403003000c0c2400490740103024060601e051b00c00140c003504003a0b17081d607507900103444090300010800004000f2650324040c0d40c402c06034156003a981d4444291024280306208405109030b17103200e40d05c1000703200f5180071100201d5002c950b100c40c2904c42d068001006031007410078540c0003031b003100749800c1d0b524031402c05a1005102e000709403284420541c80d844501c1701b18040c2d00400700443c0d091030280c40144150b4024691040c4000c0185010079038100208110a181103460206880080703021045c19402841c9540031621a101440700307440d1103c001038507800040c0151015641e10b072500c6c0642c100c00d0007902042600a0202c4401b0306000012030a24445442185100c0c041c0c1400861928404609034040303a0b041e9008500b4110100d0242845a00441d408803c1c90340c20031000807054205800340217524002c2d1035000c440880740c000344050b0803912400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 287616178 1250 287614928 287614937
    0x30f030408150c071407030204050f041a010303020c010318081201080f01051005100302090d0b090c010201091208070c05070801141602100b01050912011a030609060c0a0c080a1e 78
    0x10840124648000e40f070106410404205c803021210286500304441070b0006500107041404100b0003d802052a81c065481159041300c2c0c58000b001c410440d02c400c0c04001d0042e00104042c0b1581e600c01d4118100392700d02000d5441010100b03a6815900c1e500040b50b000040c500e0100402288a0a00400081e1464a0004c3c0003a241c54202c0128503046406120702c2032081030342845601d4465030548014400c01f4001c04043d6a0390300340707080d003540100c074800042c2c032400b07a21035031551060052640040e07204100e07140c1ca88008a04bd14000401003e0b00d01b00101459210702090007000307c0c01c01000e550b0b000081c600001c064803804510024010410742c604910000303109079001450007661507058200040c0c0c40d000d5401250144608981c666020031801c503046118801036001c4c40c5056075000c0b03126000d4243e0418540c48610031105a6256005035001512401c02c40d001004000301c0d130303d4044046d0306144d48050440c0c00981d42c2d4800100350014014005000e00c500c143d64070641c0c05d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 287617428 1250 287616178 287616181
    0x9051b0a180f2f03180a06090c12032102091804020a06260c041203030225050303070516020901060309020a0501031a0f0418080d0b060304030807030207050c030f03040815 75
    0x1a0b20816410380303003100308400c0c00000083c07017841040c020307814030aa4000940d14249580c2c140440a4098a41c056170481c003003400c00102c6560440610001c203078980c54000b0300c9004812079071a1941100c0030a82c00c160208129503003039546241d0b074000c00e8a484088002c604250040c012900304da03070031400c00d00000c4558001c0800104ca0300305001d20900345403690554511590340340314004d59101441400581801e0010035030903401500e00c0d481810354408401101e070386600b00c01182944050440d8000308007143c00c1920a40c014602d041805880310b4000c4050350200b170080b2802da0018000039036407115482149444c00c0703080010002480c00b4080c070381441000010311805c11001e42e101d21301000c0e002920742c0f101d40064159000820f4490108032107424070702d85c2ca920000e400781c29149000010307a00c9180070703801e80e07009681540c1e03480d20030b642c0d00c1410380c02544520410340b0365115009425280d0741e0200701c0030401000d640d014588961a1030078961a0181c5018541100d41e5500c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 287618678 1250 287617428 287617481
    0x20c012d06120f020f0d0804120314090f12010b061305010806030604050601121104050a0c02060c0f1206060c07090614030106080a0f03111204051309051b0a180f 71
    0x2404043c5503804540e50801003100d0340004501d2061020002c0003080e02090008501c5904040c0e0409540251182440d4510843d0a03070101e01c1040f41655001150f010b11002c2c908003054181184121a000080c140c0202e9000841e55048408402c6d48000c0c42d58050010f07503806110250046000d400602803403c241d910543c0b03958050107071001160042d440310043c403500ca10400d140e100064003c00040c00d050722142d015255407020341000d846504049907960300c1110443e405410040340c4241406440082c2061150010b0081d81c0e000d4401c1c404142144000e0001701c1c01040562000144d40d80703400e0f01100b100f0102c8040a21a9150800400c00c0003400f14081c14056486012110714614a150950301404d212014001c58840d418810a424903014001c10541c0c8084a0107040700d078219404006a45250900802c2900411030000802211700414603810b4002050054426150032518850301c5c50241820100ca4503981551800a8184560070b5039840c440d1008505003141c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 287619928 1250 287618678 287618693
    0x609021305010e010e090a020904020c160b1204170403201507050a060c140307021f0911131d0a1a010f0b030603031303050a170418020c012d0612 64
    0x1498890041c6c0000c4c0003e052448960304031038403402c4c0240b0441d107904a00520720f64071001d0300c005501030008040041050034903030040e44d0252050381c0e561010f580d1159102001558207140507000c400044c000880020542840040381007034591500e10462024000c00041180c4080c1044030403c0400148001c10000700b4005040c5400c001c02082c0541e0b03820089501c07134240300004120010210601c09099400709025070520320086c501c1019240070302004003102c0710120000c15401c611200000941000011608203284070365001810464a0242e5403498040c44408101c5030001c0d000d0b1400c1000c041c0684c901051522243d0543d9814900c11102d49040c130300842100340e80210001c0d0042d90100122030008064684a510a9940307152650b580c200340c010888409a82c000140400050708007903408803050072903040101200803601100a5018030403c80c1c3c1e6540b05e811078010704090405d000041c04140c038004040320f015500303890840700030b60810402480f280c4001404038604 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 287621178 1250 287619928 287619947
    0xa03061b0504060905120c12030a02011a0108150a0308030108030a0228080304150c0c050606180601110a051516030e0d11010b09040312060e010e0c0307050d0609021305010e01 77
    0x55030700b81003d00c0c103060401c0c509403400c0807c640c80600f10f040d2068465000c405020b02944580003030000c400e0810760042d0b220042c0703104038000740c0791600183d9060090004641c402c0000b510f00d408554507500c41402d258400d0b00103071842ea10010700340e01016410050414001c000c02e824840201d50100c1c3e40c0b40c0005021005846000c000c0046410311610410011141185540404c8000000301020b44040d07010607007900c0500072240058810700301182584014404402c8000c5a031752040d00559400e240368009003c1d500c80d1410301000104100705041080500c0b0724244128071344012800340000c2d0b40c0a0a20803d400c2000d4410740000004075011380b0100c070b085c404015031040c82c030b041c0140503040030340ba4040da0800c140000d06400140b10103440170026020710440b500c0e20f0001d80c0e46082845100c20f60541d540015096241150183d908061503107886d628000c000c1688000340d45c2590040348900f5030000343c48080100090303001c00140300038203000341c55006000018018106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 287622428 1250 287621178 287621189
    0xc0603010e0408130b0408100c05120609091023060a15141207080406050105030a0510091e0b19111804270507060908100207030e0a03061b05040609 65
    0x3c041410600a000354001902604004021540781c0d40c1c1c80141380d0b90b90014000c3c2282c41807900e200044114828000c98403c0741c2c0103450347c022034803000c05001900d603005204600d580564600040c00308042e005100400340c5203040f00c8804e281e180d803545450080030300f05912917004400c0400900c0356005038000d491281d4100500c010300f0017000c00c1c0c030602c0f407061400d100781014402c01154a8005450a010718040da104000c980e0b00c55081c159502813404d0040d00b50386c040301d054424400c964010061140c0700b40d060200d01200111141c0c058682c082040f201c2d11032240800110b0744002800c281541c10b0b01c0c1041c0003400c6a050004003902c56001c0c91803c82d10000042d0000c1e07102ca03000007400042109400312801c0e1046e1070708428940080c4112007600030400d00150951243c000301056540e08005001c412201c00c05031030096000f010100d082c01840c44c40e0001b50b5403004010710045001e030780080368540344a0030120003000000c3c1407109210080c0014030a02d40d0259072441a82e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 287623678 1250 287622428 287622443
    0x18050d05131401090e040b090706030b0f04020f04120f060c0305010509041e050708100b19050105130510110c10080712201e030f040b0a090516080c0603010e04 70
    0x10802d4012101008a0f400820f083c0c042c1d41d00b071004010703d0060041c41044003034140c51b4600c3d01d6800480030340300840d071825846456808036100c03515143e4018030070b500040b42070501e000d03580d60844110801c00c3c1025107042d01003105204c14413140303005048840b0407929040103650704020004082c0500034002400300c840c00c0c4c50741c070381d140d9086041690b1690000e0465652036600c1024039940c1071407248022001d4244110141a0f0034544a210490300340c00c0307803074607406040c88011038064000e10a148840401c520001806880e8191010356142c80c550351000801a10f40059140108032200c0600480042c280994030950084441d508400c00b0715201c6003080038402d0110242240030581440950000390380d080188066008189904001c81d5843d6a0840b505ca901460f001c120f070b400c0807403030b00c00001600003070010136042d9126010301000501030706a500e54a00e4202c07440c1c0486c1640410440c1405140030400c03291402395405c441c0c032403031503040c8002c03101403c001410040440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 287624928 1250 287623678 287623709
    0xb03010b070305090a080c010e03010e060a0207080d020307020a0308011203080f071115010e0106080106080705130e040c0801060f030f0609051507080109050a0b0f011d0418050d0513 80
    0x2511a400b144e139541c0008168184c00c58480c003126444546001946000c2800203450320050f042c1801245403e400d0040944140e9682c1c031282e42c080e40c40110100d07a402000c2100f0106102144084e500500907903009015a085914029013081c4040c2c06c88c031207500e05460040c001a5100ba80c2d25400030900c000960a0349541c18280c0c0c02d0100e01e0f04412880c000c4100540e00c00c0e004400c1103040741d070f40b61814012030741d84841c02c6e00c2e050750a0291000080c080b0000500050145000700000d405248010440360ba0303480c2c0d02010a0f10503582122001d00200d000c00c040c0c2c01c00d00030303640a0182d02c000000315a03e15903544070b6800844000030600c0b91120f00700d20902800b805000540031003240010840d182910000b400304d0007d0045800241c940b6001c00c000340d40c2885000801d83e0013034652810b2005400040d1343c0342c54080900c18440f11040002407180c0c540b402030b120148002d4048880c0e450252503d2420320080800c05401c0001c1440320610042e152554203080b00c4880c448101c60f03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 287626178 1250 287624928 287624933
    0x30b061003060f1409160804030c0f0b010909031211040311040b03011d07090507090302011805100203090a0b0a0e0603090f0312040201030b3a1509020306010f0b03010b07 75
    0x24241c0c640c00032401003c409000580b0741d49241401c8070b031160450380c1c124650380742d882403c0d1711128401c02600240300c0c00000360020f0300404440c1041d5000310411202866596078040290340e00344c1140c2035554032070020100301500b081c03028440410800c0c0600040414400d0000c060055100181044480703091084460326194408201680c0103402800030b401e140da106c0780089402314452a17144a80140061129454411940581c90f241e4941c00d0080c40c47e0011905404000e002a0400e5a0300c0000251543d81c9600403d481c05160055030b1103609090400500d001ca6a0085102a000300200383c1c90603032081e90300205080071200c0f15200d480e80e440c103500d00360648051040600c00000c400300d07400407041d00d4a204d42d100342c0e42844a2259a002c2c0b0040d40f9440c00b40c3c200f40c625240f03448400c032020350301d08034910310034420401003e0603d451b80c4420100b000b01001501d40e807000b51406608090141c240544060780d001d0b80c9451500d000c900084c0300510440100c07c5011584a04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 287627428 1250 287626178 287626181
    0xf0c01050a09091a12060919060b030106080607110303010b04091e090308041110020a030305072303010321050901050a090905091e0c030309040b032a0102010b0604030b061003 77
    0x10b422401c1c8208441c0f090a105005800130f143c5401740300350383d05d800201d82c01070700242e0284140364141c00743c07031510040050940000c0310200d04940d1240c640c1d20901d10381c0c03000d00c00d800c018a201d00080c44207040c0044043c007080f00b420740746204c0340c10410041c003081a100301190101c500e6a040021080c440710200180304d010b481c82810040c0c140103000e014180c0c481d48640c0218000c040c00c40700396042c8420003400040002520001d42c01011030b0f0340109020390701596124026007010120703100001078115541c0c81d2409605000c034070101c0148207004007100500c45072003c2c1644202c441310f40e601d000e031403402008101e504100c800520998864840c1d01001c1c001c00341d00358103207c1810031551140d103d01d0f0306642582e080d40c0c24240f02462582c001840394000c5e00107406545011140b2041c007002c3c21111903940d406200e91828103080880c60140c000c001c0d41100c2c03a440c24100d41c4d40c0024251550003140a1150034240003d0000c5000341e820a608594201c2d00040345032a000c50540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 287628678 1250 287627428 287627447
    0xf14010207140304090c03091208060f04090b0a0e0105040c0b2505030a020c0102030405150c030f0a1107050f011709070302040c0e0a09020403120809010207020a091d0f0c01050a 78
    0x140701595040340166142c000002410035030f2100c01c801d2080003800c00c011400c40d511208054000c03890310201d032414a0242d020140c1184000d800b8034000c8203041c001ca015038103111412180c409811040054000381da115000c0840c1e0300d0002441603003895101c542e06082c850140145800000402c88100107880480b500700145181c90b6800950b0700b81041074503501302ca0102c0c1d015005e25107010003d50301c04804c480554000400081d00c41800d07038006102900041440c60080c402044000c01522440780907021017034007a82d45201c8054000c1100b41040c800341d00a500840b4a064540305a82e0420f103104160303042e08600400980e180e001c0e003498580d95500103900689070242081a0700c0e401060040c1c01d407c2510b00c4130140c1d6440311150200d104900c0003074900705c2c0a000070540d00303104050740d40d04140040005030a141c0d03a074000408a400c26400608995541c201001c150700c1030941050101240001070030900d1030307642580f6184d010004405040140c0040d42c9001107000d40a00c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 287629928 1250 287628678 287628683
    0x6060903170405180a1a060412020301020d02070c23010c0605061903052d0309010e0604090203010e060a27050702070f030b07140a12020a0507020904051506030106030f14010207 78
    0x110342d0080030710b000300a0031200740c0302c0405e10b508020000180d240403449000d18000c020313000b01d18052402d00701c0241f946003028126070654080040c01c80c280100e00150001a010308030b00d51105140124802c002004600450046014214401001ea070810f41d10034040350804d0000c07849035140c0d000030b2154504154248405204500080240140003404510f240821020421a5482e440071101000401a440d480c0c9178020400100f00b94030070f20032500003072400383c209800d194a40020300240e0b04260802190460740700c3c200300052910320081d500070506c45a00d48440f40060900ea201c441303400c062800f20303548900200b150b841c4200b1038078000f00b040c1000000c6a03500d903e8001d002e01019901000010b0721055140040070300c8408a03511042c59803281c03240018146031140c00b80d00081c8010b0300388441403280c400580c0310400003500c1148920060441d403480c0c641110301c240300190440d40282c0c034080c41440000c100001000790705801c071070f00c7d1120301c0b480c00840d40a40f1800600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 287631178 1250 287629928 287629939
    0x92d0c1c120206070305011202030c100212040303111002031905060109050402180a150906081b0c06040203060a18020d050a02040603240903080109020c0109240f06060903170405 78
    0x180440740e5800704800c0d00a804555090041d0303640d0310206911220030200180d4150005080004945043d4032810388200c09801a10104c0c0c59012040c0c4083d00194403c0d00030a0345038828040b101c00911440110b041007200441c01c50030050b403c20b48070000d80c503102174065a10004114681e029048410081000030015541c800c0c1902c41500110030701550305005030400d06020a6120980c8400d240c00c9510f5a0741c448118500039080311034031300c05002e903403015501300d41d0140070000700070091143d410094004d00150501c0d205252510030010103c112603440c0103034503040905540d8203560080d8049507803640e5090035080003410310203e8a00254031a00c0e0900001c20082820350200c0c01048401013540750700440d950308820307681c941400078001203003180140030920755640644600175002c1e000203400e19440ea650094000448032034000d50070b514081444210441c011401c4e40e42e114942880450314180c00580030310590700008102c040301000326119070074410281d40042100900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 287632428 1250 287631178 287631203
    0x30e0409150603172809080a06050405061819030e120109021804050a1e020a0308040f0f0b03060f130f0203010311090402010f0509031203092d0c1c 65
    0x31400041006103c1180c0d400f4070642e105054424030303415120303250841031420540170f85440e43c08020601c0b0031403000500c20340e0100840d8441040041070b91440c03103540b0000d000e080c141401e034580f01f0020840341071100c02271070184001c0000305619507015140841e01320302e01b8003443c041e1991140070300d10903009059141210340c00d400540018080d24000d840041c0b0a200c04020210502000c440c09026075000303950301000200b140c0161070103030b2042078504140035170a50000710140b07000d500a50b010680458144155400c83c101c0b94000e0000c1900000c1103450600d480c500360000601180c892130b16160028001e480c0c0c0c11038200f00240a803410400c1050130504480290404c2c0816600049884160034843c100400060302942e016100c029138510410380c102c615a00a80c81c80c2e4043c098141300980380a5024003440c052a20900903000d043c0041814030f90010791180550016020a40300604010001c60042c2e140740c000e9402e000d440d40c04d10328640e450000007a00402e2a0034480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 287633678 1250 287632428 287632463
    0xc0f0302130503240c070b06090402061b010507020f0718150308161106122421150c0f07030c0b01030818150a05070203010609050112030f05040e0103030e0409 70
    0x55140d1420072a440140b0f10030780b901748a22600d801011001880d80e9501c02c04940b40d85000b4034002c0d0b20610003048280307405445601076590f090380b07000c450501d079100c20030701030540d8041c08040d1101130404001c00b441850100810010b84191008610701a505e00095041c5031013101e08001464001c9215680c500500252800000701c4d10f0059402800b004104504d620f8064110345140603050400348460702d0b9100310b41c8403920940550340e803812007000420f080b81c0381c2c4d20300b04007a0040b044007007104131034401c16641030003440f801d1125184401c0040004140b181006c0d0f600b4120018034444d21003144e8074060b100b100700c1c2e9002802685e800781c000001c002c115002013007048a40507040005c03100741e4042c4211803010900e00e90340c41105103c0c5649040c49036024000050005001041d0700c2c0d078a1054200b101c60a0b045900301c0003001a104040c9908166408507403002490118600f615047c0140c0e42501c040c0402802c00249040400322940c41e90480e0036550b8202030394001c03400254 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 287634928 1250 287633678 287633713
    0x204090b090f07050f010e13091403041805060901030f031407150e0f1209060415080610020304290d05070f0e010509030615061216120c0f0302130503 66
    0x54441d2258429500003146605015041000c17400c01a1548a40c3c1e000724010480d001d083d044046a0655848040101046060013448140348451000c4e598a90510b00d8002000107080121200c07981400107225683d1900c1e04641c0c110303038221580e94007103201450101e4820150f4002d19050324408600c04090012448000102483c500170811100d460400d019444181014075164140c001320585100009500001c100811380202014130b056203c106a200007521038100e81c001506071000c0010078141104644041501800150700b46894244803418030409500c43c01c01a004403558804650740c01c00589441c5c1080344400d010030f28044d240105400e0211011760000744044554441d035500440444200d940040c0103480640d594940402810a03000040d5800010030090381d41c0d5950032440303890090680316113051128042e0395005000c0050b031010900c409183c114a941400d03042079081c10508180d0501580b104400c0e02908082c6803a940401c3c0c150240080c81c6990340740c10f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 287636178 1250 287634928 287634943
    0xf1e051908030316080609060907080702030906131d1902070305090d061b140f0f1b0102070b0606030702030a0e06040f080609060c0a0807030f23040507060f05070f0204090b09 77
    0x55510440d91b65a0042000710365402a1102500101d0342000700d000c0c00d101c0c070700250340000d0300c0c011280b8242501010850790343c4520031317051150a545e0821f010109040d130800c51041c901100440880c1020000c9044941d00b41c011a03102e03035030005015040500400581d56640c00c020000c0c00080e10a04080380030304140140c3d500f0440c0c101ca0202d1416001d00e001c10107500c240c4545508200c009805071546a202c00713946003102c1d100340041c0c10f201054444401c1256408000076865035a580b40c0b01c100d880c0e000d04880d1042c2c00600402c24050b60010542d01440c6d810b1424550541d0b00a0100382c030382c0f04540141d207062081c61004100004002100b5005865002c202c3e00541c2c3c0e500394031a114040d1003200400640a81c0101d0313429886030308070030780c0803e02c1c502c0040d01c0b030b484814003558001e120403d44e00b9541a2006c00050ac0002d0150344003c2040e4104070083c001c0c0681c00510a114901c0010b080507800d82d00507095449a61000e812168040000492810074429081c3d07201b44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 287637428 1250 287636178 287636221
    0x604020a0602030c0c1e040525090e0a05190c030e0f011a061c020a0c23030f0d0e0d030b03060106020a0803040209070215100f1e0519080303 62
    0x114110002500c0384000f048807805849100a1703c882142c0314100075120020305100e034910401d0314a104041d5669108040c0036041105851205416009071519008144860181403066158041000e45692000d82d40d0100003514005502d59482c6e802d0b08804519034503a00c600341c075000f900c8002c550564800d0700c2019840c0210f03048084107055480c245c0e210101c01010303604030b1003040e12031801c2c0000a041048a0000d648603101204940c81e012030708034081c40e40c001000d8605001c14020294900c441244401c1341e803c09800c0342100266981c45200c44000942130001820403006140b0f502c083c1d85510b0780425950000f415007002005061601c80f001d1190050000000d01c035070001030058011540100c40c82c0c1959116000c00803e0080108401c0541c050030002120340c44102d11203d2064071955407c0c150103040ca2400c242c00700c078640040e42400245500b04100c1d48842004600f1180102d5600e002c090080400d04140c0035560b003d24682c0c80003106008000c0304900340c0c42102070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 287638678 1250 287637428 287637439
    0x3011d0708100e0312040519030207050f04050405120d020d0906051b0a090302010c020a08150a0e21070309080703030509040f1406100e030a0b0a0b0402190302030720060402 76
    0x4481d51120401ca444507500c411544d4010420000360f00303411603542e0343c05802441075a40d0310161361040b85207520504812070040c0c000c604240034502c1d201020418560090b5405c10088ca0b141c0c0d01c02c1e58a000c2c0c4003030344240c114007181c5442c00303082c5501125280111464140440080303450100043c180681d041000310b450401340100359840d90058035803490b19075903203903d041d2668005540742d5080c0c1c80203a0300400500300104040300100300c4e070503192400f42080a69850483c41140840c0c031400e040c00e071250400a41c00c0e0030348a01301c14902068059400c0c2c00d60315809890203440034582ca0303118400c02c2c018102c0020525400c00c02400c01004143c1d810f10103082c000090000f2907480c040d610500c1032003440416840d04041d450300c21032405a01b848441404a4000a442d1082c040f40455500d44400204400701070140542d090300e19040da800d600302208102041c818844440368a0101540400000d686030b1080541e41c09004448040000e040000950a80c039400105c03401e90144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 287639928 1250 287638678 287638693
    0xb0306090109181203140f040303110301081e0120041a090604030605090a05030d0c0e090903030412020c04050c0a020c010c020a0512010f0c0c0c1a03070e03011d0708 73
    0x18100e0045000c082140007040500341110b40d9410003542810b4400800c05d669521020041152841d18030f0143d420903504002d07902c1d242c0740003000c2c1d50308040d82072150141440108a29440014a82414071480040c4032560000030032090040040d80d80072000421004070701d22038200440020025030314074401c0192641d080681e80b148030300c41c400d151a000b00d01000200081603a0b0345c000c2d41c000070300300c00b5107500d5000d0b41c403614915040400301c145403690310f4480d40e00e21504403038815400304041d200c0e040c4a1a09600d070545038040180003406003240c01c82c200a08910902c038003001800b00074000c100c0f90801e00300c41011074000d24800d0380580320f00726888110798007607042c10002c26801425000481e040c4028882c02141002100c101036480d200040d0281718203000c1c0b00c03e11145c48d503c01040400504100401c82841d0380b01d00ea42c1e0300449499004181140c0450f0383c02081c6040c901041c50308400070030b00400d182d044208180014007070785a010390000c1180d4044410a00484196 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 287641178 1250 287639928 287639939
    0x703020a0602160b07050711010e0609090c0d141b0c07090e0d08070e0d1509051212010e0103052a0306100e070e01051b030906070605040303060605030408030f06060c01060b03060901 80
    0x50b44a01e40c80a440800041500100356104d42b054850001002e007001d400d01060070003050000c501598001018400801c0071200c5078543c1c860101403250103014113455040c07120700e542010840102c0380002c03410029940e10800800c000190090000b00310030000800207104c0182c40750900000c0d035001807001808910007910404002210f0b076802480c0100002c05517a4000d5003a00c000028076030546c580c50400c0c0400c00a20480030b01d407006822413a0f91310050345078865130f0b0805810490820a84038018404035000107001005192400c4640048009914200c88228604c3c400ca540c148100420042100b4065020000707d40000e09005019203c41c8415510031030580380142c0090400c0c00100200030a101002e40040d2000f41034a244c1001e0001040644d1301000040c0ca58a0b00c03501070004240e07143c82280000c1c0020310b0410b085003401e540d907540503c405082d5043c0d400424010407015030359107040f40c006e615103000800c2816510315400d9020340049548900c0303500303941c00000d41d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 287642428 1250 287641178 287641187
    0x30c0103090203061627080d0201050f070c06021323090c121e1e01080601032103110a0c06061a040315020702060708040302031605060406050703020a0602160b07 71
    0x50301d500a004e8100d03552100b1403a220281100191010401310420a41c418150400c00c09884c40714100d040c405c65007009100f40c03504080461100c00c580c5040100500700044203d46070f004202d030700d401c110003910350414501034003e0600120101c03442d1800002e450301640c20b070340104c100b6813014001429460080104c00d00c8222418518800c080000a0403030000c6d90840d503009481c40340b5100f5078540046801c540b04c1e400c03103840032010702c40c42041808048800207640100468001090340d581540e40750303102842891a8040190625205410141c0c040d0700100c00803910029101c0e102ca007100c00040070f010b218034043c1ca41a00c0c01c07602141031443c050006201c0000006a54501485c5642d041003200803410b2070001603231701340040c1e001030ba6508001c0c107040d03002d440701546482c158010107040264007000010203000c0300f01e04101c2501c4030004e4500301c3d26541029500c5413001d080c00d80c1820050380c070007814503100003050118000f0459444903214091004440d40d0303038a000d029203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 287643678 1250 287642428 287642441
    0xb070c020f1219030201091b0e0906160e010e040920091501110a14010f0509031602040e030904090b04140f0307020f1c030305070807030b09040f0f1e02030c0103 71
    0x14255040a41c101444070a803c600b110702d14800d02c000915844c1540b02e010008607418480c010190600e0000c1101d03041c002001900b21481b400030340b02e5070804284496601c04004161402e1118400d03d0480340d80c015141b06c10400c0015000340b00c103103d6442d200d4000e141c00e442e00c4c0300c41c18a01c201c803615802d05070b040720311030004d41d400001c4901c4a00015540803a80d4581c0c00503d01c910b031020030010706103d082055204030200003103030041c0079007240b02c2500c5c4018861016640203228084810421804808075190150740005045880418240c29480742c18046030300f1500b88404e4108000c1950003a5200b10701a80d041c1d981c0c40310b207800e415111f042c42d50520f02c8603401840010b01500c0c040c2c503884000c0307000a128102400050580342400c0c8900481540404d42d180108802c182c1c0144078941d002e40c170341c82c04201c44041103002a000400c0580301900303140c11000d011042000c072003611007503141c2210402a0410300c0c04040e65050000721030480c001d00903404804065400307030185c075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 287644928 1250 287643678 287643709
    0x50a061d060402030a09053315090a1d03040510020606060d0c020a140d03060e0c07061808121509010b0403030c020d06020d0b0307082b0c0b070c020f 66
    0x21240d403507a4042202070f401c0581491091340d0380f0045c004c0066002c0002c5580c00700e4400345080d00d15800c0902900c101104071500403414400000c01c846414800c071041310300031702115406402d0300d503028014010704909400381031540c0c10719184d1168a40003c085c0c405c4407421260f58845542408040f600c0b901d007603d4264201340184034400e100d05d000c2d040f002200c1d61034812a1103465030b640380c1815000030f00d08010b03030b980c01c002d01070780403c0d81c1401414058072841069090508003409500601c1c13284c071202400a5544004164801c4250a0402c1e001600b07c041075841d40608025161241002c0e00c1d506142000148002c0007810300c090014105d0f00d00c1184681010329588050b50221791070242242e00a520807030850006d902071000e0700302c080c440240000d1012030310b000e1600e490100d41148440354003c003982681c2c240703401301ca540046205855031030340080224058a41c1228090010003000d556010020a01d40c40740403410f14030f008951020300003d042090045425800580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 287646178 1250 287644928 287644979
    0x5031209010e1c02060d2a080705090a0b0c01020c070801090507030303020a030209120303060a0e0402030601060c1b0305060a050c090d0219050306130201020c060c06010e07120c0201050a06 83
    0x1007820510304408150a60b48000ca1101c046010541c005102603004d450204030301503959610499250304e1481e8103109611f200e081e910207081106001e02420300040c034210400c80c0000d40d4000c00d4444032040801056081c0351103494407a29806a400303500210070522840c23140c4000012144014095682400d4101c0064000c13541541c038210b0182d4841c00855042c1502000130805e0350703e0b8000d40401e40000b403405076480c0c0c2003880c1003100807001948420880050041408050307078000c1072150450380141000e1400310f04505d01600841504504521241c44c111000003e000380030a2052184441c01e108100c50341d644421081a0f00030703501100d4000104400040c01400c0c008400000340090b0401215810750b507900003031a1403400c4a410141c582011000700840d6010800307400400011903e5a080001820155a60ba001403080030321080244003c144814000c4522040038030340c050341805940300c0a00c0c00f0b406400c0546175600c1403490601e000034018641e081c0c50081007918400d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 287647428 1250 287646178 287646197
    0x450106090603110912070501020606010f0e040902010e090403081e0423071a0c0106051c1e06090501090302060a02040b0a08060310022b0c050306060310030210090503120901 76
    0x1100142071810102d0041030f010403e10b1015a80c0c804842c000b054034000500c82a42400300090030541c3c00352a66043c071409000800210b60448001045000c042d140003402c4112400101e0794801641c884a8201c4404000c0c8020715510900062140c0c2c0c0a4000d140c07091203040400050007411a40074003400110b2903010a00c440b440c1c0741c108014404011912105c0d00c440284411003882d4510741810940000c4d0601506001c1c01400002c103001c4503080d1244020300315103503141d43c0302c010003003481d03460400c0b4540010f0883c0d50b050b107a03504001d041101d1140391400350300910340d035441500503120b0040000e03007444c0e041c0225010303569002c1641d03081080408090300d1112014052075418041c54091880300030462010b0030448440404510340c2c1d0300d100000141121400d4110050b441c100140c0e40f91003504103003280e03004102501c20305d907656102401023a040c2c0c03090300025440400143c01030380380d6034007810f0341003554401c03000d40d48602c3c0380208442e8a4482d901800d80420381201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 287648678 1250 287647428 287647439
    0x51806031b071b090e010e0105060f0d05161d060f01120e150f011806030f081c0e030426190f140607030e030c061545010609 55
    0x6040014403640d10280707030740071411112003c00403a401081c00b550f501c280007034041d0402d00a94903801490402007200b81401d034045441212942c041d030740074010000d1042c0800404204010442d0040c548003010035407210000c0881054242449880b94517600120f401840d2240e000c010100050b125030070700f0b11040342e43e50060a0f1001d1201d031320307004501d04981c06582d4030103a940300700d00525180d061907052002c65100741d40b80518a10540d4580001880046d00030031108034031507042400305440720302c48003a920041e000d03150207a0f103c84c2410316103082c45400001510036225000c8080c42050840150030305c58a54100d0b0f1074003243e10003085500c020040020203842140150240701e0401407a48800746030013402444100254800b0f0100142c0039850700c10b26045036116030140d4078092421a86c0c56070b90001a02d418031325054141075903616594a0714500c00d80d9100c0c2d00e80c090481884004c20f1841d056a041c0c001c60700072103003a24100c100d103214414181d80903512411110350628 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 287649928 1250 287648678 287648731
    0x32712080a023402180a14010e07120b041407080c180603130c030b10061706040e010e0f070e06120607050306062811010c0f1b0606030305180603 64
    0x80b540d80420034080702c3c194090303118451202008143c0718100704460402d07180301402c641d802d160700c041180050005000380c6614403042a0000082d10300b10b8110311980c50020700500c003080d1104d912900d0000c0694119540c000000d00c103102940325034082c0e40d280da026078614424800d1800c0001100865000c840c60701d00003440d04013020402c00c0d44140c0303e41d0788995030307402c154000341c918030004c408101502200c20414005003c403458100400c8001041d00c14551402520b0301e4411a140c4682c0040c0d02400d61040003600340034006c440303c0400084005468103412302074028030022080029540313051558070180200003500040090765200c030401c4915801c0545180d0f80002c00f0458141404208943c2402d040220b0401c27600c003848120b00a008031443d21071404107641040d41c2a140c55401c04103041ca50316640c208540040c1d2a9a490554805000c1d40205920702e494004000c0c19480000b0f0141c8000c00e41c0d48040d1461000e0411125002c100c4034241c960f0b04500c1a9408401c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 287651178 1250 287649928 287649997
    0x130b0c160f11041508010c0f050301060c0201020c09010f090e0309150a110123060a140f0604150503060a0b030105090606090402070c03141b0d03032712080a02 70
    0x282c5010107032100c0c501c000340a8401302410480910b80c484024000c00200307110b41d003038580047c10411005642d0101c0540700d4041441002c0600c00c4c03100d940d2040d640213124070311b00c040008024041d19a150b10b1044900441402811200f40c5007100c81184403000004807441e900c00100160001951202c002405070b0000d0808130170040050440a07481c2030034041d14a00f001d684545076885c01c000700c1c6c1c0002072140100100d00c2643c40c4e0b0020004550314110010006074161801101e04210101091040c4681e90010031101500003481c0b003141d5000000d180501360868030100150f95814000780203000a009043d0310000c0200400c42c5803900400420121101030005400c0448036100c402c0103000c554400c0d9520002c3c900501c40001d0240015000901d00181d500c00c1410204040340303448800000080a0581d1081035510b0743c01d50000151141c042056034094151031031074031079000e08450148501103603505010840d90221402680c10802c030050325917561050050243c100b4a81 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 287652428 1250 287651178 287651183
    0xf081e061207090209090c0313060c051201090504020f010c0b0c0a030908160311070b090d020315040c0905071b02010e060c0d090f080a050a14070b03130b0c160f 71
    0x1c0600700c0407030070080c000ca070020030190000684030710118051026020006014043c40b003c1001000003c210714650817416580141001031802003034082034a00307128000c40c055929010030000114a0780303d40002d880740c0d00c00e41c5e9501c15a07007400c00540d0b000c041004002d1414115500141e012400c4802a054902e03c03403401003070055041d12011442e40c04128001c004071000b0020200313154022408800460740c10b0010031a55281500c0c1030b28078050300740e5141c4907155168074101955020420703c82038080480000103241001d00e46444901500d100b140320031810400082e52090088924554402c0780240781900303940a60b00460344480c01080d841c0e8850024003030720b901c19000704408411000240c4032200c070241440b0386c1c246500078036808000d43c3c0d417095000300009540400d45e92060f56100074a6a11003004000482c2400d40681103501d012001204000d9082c0070700c2426107042d4000d0714030403c961a10b81011080c1e2082110a2041309800011040003500c51070107840c00fa0b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 287653678 1250 287652428 287652439
    0xe030f0a110c06040303080604110a0e011b060608071502062e0e010f0f290c071212081e07050703092d0b03070c0b15030610060f081e06 60
    0x2120b2034001600750700143c10550000c1c0c503403030811090382424420b46414020280c4400d040c4001205d0040030319820407020340c10042541811a006c1605040f0b4600700c66105000380480394a50b1541960744900d03129030000170302c404030501d19250010407094020310161102a0401c01c5285001a41180c3c070030301e030180c08030244000074a0740324800d42c41e4040c162055491620a1500d080d003103008003030740c00401da101d0103110901c2110400d5016200765206d694034860702d032002004c03014282500d07684004c03101940c500081007000b590482c105151406c07a05c03628055101c4019040c041c4041d403010640440700e81c00402c4525020360f0141034603500c00c0c1780a05038a901c0e499020341d206055113450013410200c41d031b10361110601c16105000b8040c070500c201e00b5443d000c01d00030000408181c0c080e1503504202c01107200e06141411114017030314064201c561504150f1400003480419100741000140d103c1c1040c00f80502c9004c6041c011140b91b8170220180e84400c0403407030360220243c642da9100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 287654928 1250 287653678 287653693
    0x3020a12030e0c01090807120201020a1509021e0306010306050901091a0412050a050301091503082701030207110f010219030804050d0c120804030e0a03060204090e030f0a11 76
    0x15045500e03060100895600403410041ca026030a00d0600078007200e0703052122584050001c04d4000480d0313402c07a100f40c0c410358000d03106400180c2c200300a002c1c000c0c091350044481c1c107940f0a60f6810030b25641c8e20a44103225030366500390380403500606425043d40c0c0f60700890010404100a0f4006d1a0410801d800010b1803484a40d168410f4501240c1005000e0846001300400d12040030140b4000d041942400e516003401d03c0802045440140a0540300c0f55503000c40d000c031501c00d0014517003d0359100510302d80d540200300048000540c4c04a2201020100b445104400d51080c000d0340c60342c9900040042580000b1010402d203241c14915460451240710030501600e4030807208652118002d4541d8451424181011401c5c110700d0402e010034010208010400207084030304140c8903849904d09100c03140c4441c0380c12201070340724000d01c0f60b009070141004000c1c03288541c0200b048508030030080041c0c1c60303055005030300d83c00fa55040902e01c660601c02d0300c0b10680504502045040a0015a0a103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 287656178 1250 287654928 287654933
    0x1a0703080c0c030a02010b100305091507030908032502070b07060f0902101e0305040305040e070306271a150d1e0501090e0a020907110102070c08011b0c08040e0403020a 74
    0x11031304120002d0005071746032040c0340c98a04145002d004201c0b0382d89014069441c01c2c901a0740c0e92220101001c001d1101080014442c41c400d60220010a5100aa1036941d003000d00c0100d05180d000b055412a010000c4c0710300c0710241c0000340290482d50f41090050610000c3e441e104010044615240005901c5130150001a55601404100d200c25521003d484016a410701100038400c5400e000926140c182880301003038000d000d0710f040710b841c542c0c81e660f59a100d62046021701250b81c4001c60305001c1c019901ea00c8030b1058004203400901e0b140800291810141001844200f0045250071a13107038180307004c0586083c0700034000e20104c140082480e2000c00000e03031009001265012403a9550301c014482e0304003d000c4c03810207101707407002001d21180c550000b071240600130b0414400c0c400030110019803d00d0079015580265044070115400c56a42c080d001d01920319811500000c000744495009510b014402441c20144c12075034050600341801500b000802e40a8820780a620600d14179a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 287657428 1250 287656178 287656183
    0x70207060e12100606091d0109020d090c170d0302130b0903031c0207021003020304020906040b0409140a0308060303040f031e0f11010e013b09040308010f1a0703080c0c 74
    0x100043d00000150186808030042c203a4041d50004280303035100380c02000c0c1c194102d6040506442c040703040140e96000f0ba040b040020070048100400d140c4000d000010710405c6c1d2000803120007410800d880070502003030f070704800301d200b00c1e0400300603443c040c003003030014200100160080900143c01c481c900030903100440340230014005140e00c401c0d0009149000c6042c410f044044541c0344d4141035066050a60000d55101c0c3d000302094021651040500191f5585412020401b03070098040031080010050700c50305c80c03101c58800e5002c10040d00205500d82000004c9808540c0b151300b11294141c2981d5445510355040c2d00344403140f03001c0c1c81140703010400345a11411034521503040c0e200945140320016101040d41d01586050020030300c0c035040a00c0da03540b64a076115801c4c3e1032565101560b00c03035100032460004000c513000742032007040208168001006c04d06031440c00e0344a41c98290f42c0c2da5000301104c2e1320b22040320154414030650001070b0003810301076002103800e501d082c144880c1040039071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 287658678 1250 287657428 287657443
    0xe0c0901033c050c09010518040c09020a120c08010803030415021903020c06010b090d060e0f06180f0a0305120910020f0409060b0403120c0503160b01030317070207060e12 75
    0x48810482c99002c0108a003c000403041c800003555403002c0c6601d018006219031040c81d020080c205003410001d002c006000c44100080d040111045459442242c8010079201c0c02d19000784003180b0308500c00076080d02401e8428126440e1000541c0741d6a42c0e55a044802c0c00c0300303840031036100d8080c040030100c080500b0002854803242d980058542c4016288540b4007070040e07000342d20070130040040d0348481e11118230501c5840e4000c01c0200c0d4509075400c4451a00c0040210004180070340801e00c403410032240d109215210745032085801940c070035980962100549500140810420400c524028045820f019800800a0292030111402c02e48004c1644c2c80380340b0388041030030001010700c05140f661203640081c1480000c1c5504040c02c0d40c2c1c2d034515202c540c1d5410014800b140e0042820072008200b141e0b0450711000302c2c140c400f0518500b00448080a000031030214003407080110f000f00380d8100c00ca10414003030703000301a21407500e0003e40340318115001054004100351112240e0010030400c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 287659928 1250 287658678 287658773
    0x302060c15011206050a0b090a02180d0b19050c0a0f020f06010305010219020c0a050609190f03060c08060f0405090a0503030115090b0a05030c1602090405010501090e0c090103 77
    0xf0800d0892803030140d0881d0401080300c1c0840740351170028592511200c036080e0384982e04407130042e40c0e002005142c0c800745a0f5160b000e80d101c80c21015607030030010f000e601c031401380c0e8013100a00c1400c07080020ba402034032011078010742d0705541030154620700381c4104110480c0e41010f0066903a009007480e051400d2100907001903030169000a0700c2002042032910040c12440b02d4400307402500105000101c100c4228840c1c1442020041044480d0f030340d131458612aa040254034582c142503071a04800305008a5201c141d5055161142444c40d49020f95446441000c0040024014880850802000b001c000e0302c2030795940b083c00c91580006004000550207030041400c80b400d012000107004002006e1a0415032184d1320a002c01300354035800c24203494108024a40d40d50310b03a001c0d5110a070300d0508884019621242d1401803006210041d4403142c1079640c2c1000500c8178403603844085944100d40401070b1780003164080100049a09080003440c40d072400c44a100503480780945c41e20412a43d072006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 287661178 1250 287659928 287659949
    0xd03021312051b0a060e040911090103030c060501090c05030a1d0109030305041202120d0209060d060306020d0c0801050303070201030522120e0102010915021b0712020108010e0f010302060c1501 85
    0x15150f04040441190f0706800c41200e0040d40d041c1045002050080c0b50714500c0d0203a501c81122004110b031a00e404440000e015003081000c1da9641402018611100800e9512502d04800410b00c6011809480292030264485a29607200d0a00303180c020305160b000e070081c20282c003c160003000303800e01034230240728020340c1d000c18142010b09004881d03400c008110819540003070304c144500c10520098803140710b2003540040e215208500402c103144034240c86114614030700000801000b81030350281c803100394000c800700a148040007003558000401e0280310b0f81036100303014aa00661081d00300590015080d0325101040e448104603801800805008a426084014a912803ea888481900103000c00d100a102104254482107005040a890203112031740000b4150b031101c1100f4000c020708c000b410300311164195100040191032544c08822400546070f6800015040743c414070305400fa82c680c14201090344d21315400c02002d03521003250003226010300c6c0c1204901452380c5074460300800c8240300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 287662428 1250 287661178 287661193
    0x10f0306050f0402092e0621060627051915031103070e0303120709230a30060605090c120c0a03021e04030311060103050d0302131205 59
    0x40c84019035600401880951a10320100300240c1d40d0f03000c10741c0e00100048001c3e51040c1c80400c910040b00c6106042c1000c03e6030b0044005026035204000351610b03d40f52030340c101c0c20040021500b00341c84040c4101800150324500504100081c41c503d08060412480d100802030340d00d50100b000c101d0680c800d80d4807501084010084200c0b0040d400c8800c2c611894200807a090181242d4418000030b419081006105450405151010403c9440420210140070314502d0b002a0007003900d540344c0203005941400c03c601c4c0346190304034403950144440041600300d4481c01c14045d030420b0448124110f40c00e180c841e10484800c1d203400c00c0c042445008040105107541001b0078042e01041c00b03400d410b0440340411407401500c408129440d0803501c0c100c000c950350140100d0440103405040c042200309507000c100d070482488400d000788110b9109441c0c1c0450701a24504207512003001b444042e0031504441c4401840c144264000c210b42001010f1a210050b202c810410004081040c112407d034008403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 287663678 1250 287662428 287662433
    0x17010603050c01090e0408070f06050a0902030c060a09150c021816081302010c150f090c0602030f040b07060908030c1e2b0902030a0308010303170606091011010203010f03 75
    0x40902d030910428281100c81524000c109040480d008001a0a80c80080707031040c00c00c4411859980500e4000740c06001c00c0c01d1045502c00108141e030000c078032034482d06200c00c8503030514000b81c0e0204c111075101c0071001407038180c9501046545181100070480001c1c00d40005a80354518500240c2d481010006580341c196207240700c08201104040521900344104500880d0190710043d01507420702c1c212181010074a01140881c4002115403822804c0040d07030140c1c0034070350f4046141640141d50404079150b490605076100c0c4260003511004200411052068003660b00090401c90311549000480c1012a1207041c900d420984100014010005110506040e03009800064040314400f503850000c40701a80ba220455140c620002d100304181c0791404441d0540c80081075540183c00c0e210101d02500e002002c8a900740421408105416a5550300b12042d50841c0e120300d5003d0140b0345402c0f8000c2c20001c4594000c19030804110b85000c02a000c40c40a0018500800080d240c2048a41c21071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 287664928 1250 287663678 287663683
    0x412030515011112030c07380c0c0303040303020d0b0a0612091416050910031e0f0c17010f0b061602190b091e010e04020f041701060305 60
    0x10400815040c802403003070902500e20310000a40003400c065402e21030150405062041503901e50300244004010000714148030f4000703142591040041520b002d0326911940306d80a84086010305d18000ca0203451030800c0c4082d410354000c0c9400002900b04200c0d0302c2183c1c42d580c000c0314101c0000b500400e80e6240f420150090f00600c4c80101c0d0000102810014020200035001015180305901c2d84459418012940c501e0300c54902400180c540c0180703c030868226038180c0384503160103100100009140ba14002e072841040e2503005501841114922803460b1500c000c0c56002c0e02c4198a0b0329000c00010038001d000401050303100c680e01d50369101700300d002e821101c1083c0030070720140c01c00c64010155942c240460300b41c210040d00364104180103001050061505141514186c220405c0100c0c010a06501500240900301c660700920400c503039281c0c5081e151301c2413403070100b50b4240001c0c00520f041e0300a0100301c10610a1582015941d1410310f0400d0003421000d0b4003655035440c00d00621206 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 287666178 1250 287664928 287664953
    0xd120501060c030f03020f0405030304120218012102130c0c150606020c1201060b0f030103110f0319031209080408150105030703080706090b010314070510020d120603051504 76
    0x340c1c01c08040004841d00c01070011341204400404140d0b0000d51100440019815200984809000c8a80341c81c0c8400102c2c440ca441d51400fa40710354041000d1142c280380c07211085059904e54000e500e40903401259420a802e58894220383c05409201300000c016098880ca01001c80103542d40801d110355400c0a1034150703842d006950156082c0740c0306002294001551b1082c603001a103ca8941441240c040c40c014001c47e0004204140e00041020482090038061416a8010840c0545900c07a0108200e0090080c2d440c080d011b801921282120a40880900b00c84034028208820030307180842d2590212200100121003c00c0c000c141403248135000c21111008100800c9082142d504140c0000c0d510409440010302e0a540001e8800800500d41c100490b5154000c0d02010b565840340b900006500c141084c51915100701d40001070130b03180145200c02d0307644a940292240c2c858040e4111468080081c104521036218080000061810030502e802c8603c030041004407070030246082d5030040407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 287667428 1250 287666178 287666189
    0x32070606090b061e040e09062d01030204020a030b030d0c0501051f03020d03182c07050f1e0304060504292e0f06030e0a1a0c04080d120501 61
    0x6840502d41c82d070388031041144d0b9002c07070703a8603d1071006514681d04440c91189400210f4140b4a004c1031001d001c800242c20350250041d001c210341c03400408040b0040c1c0b00260f0806059a6088400400160900740d0040017410b0b410301d000303c3c0c42044000441e01e030199000d0144001040c038100d210038010284a06504601e000d2168111811046900754065080380000b030f00c40e428082c4888205030240300c80c0c5030030100354080c2446051351102002c1c1e07180c0c0c00c00f508882038a1a004550b180b0310512202500c2400c140c0c60301400c11004400340d881d150840c240011543c840d04086001000a0401852150348501008922850a490b01071000b0b500000c41c0c050060101c0c80d00420720690352003637907008100824042100c200e68805a01a500100c0040c000580d0030310041a2039843d81403c0c0d0542d01e00303440c00d000b40c1300e841100d1552140818405011042000385403400310f0681036000c3d80003411308000d18202600c4c2c1841a01b003d004c1110140403400401012102e0711450040c54010003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 287668678 1250 287667428 287667431
    0x20c09090705040b0d150902090a0c2f072903150105070f0b0412020f031c09030e03100b03011401080c09060a0f0303030203011806080703033207060609 67
    0xc004081568800450060b50702c10b40d02c84045004130f41310f0b01c800c9425990014208240b201d1402d20020080c06559001d034000c440410015602a0042c02054004881c40d980c204041020000d220740c09519600b684003e41d10960400390f01e00e10420409000d0414018252020100b61300c0048419040e4504038040540070f200704501c1c1e668420815520700801c0c20241c3c0c0c3c4140310710340b00c1c1081e0708001000b0315410011091000b40030620030000507001c4150221421421140f07d025070301e001d02107415034220041110000002e496170881110705120742040039406070030000180c2000201001c861138282e8401181641c2e02c6c090103000403101c2c00100c1501c041d41058013486c2c4407600e143d00c6500ad0b4030f0b07a1012a409480e060106001407204140003001d083d02d070325005019600038403904c40491082d010f415001c0c05540300303510840304040001c01440d461640c05940002c4821240d42c0c1100c0101c289141c1c0070305485008a8460450740c01a6980409151900885003950002d8880c907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 287669928 1250 287668678 287668681
    0x1806050f0301141303180803120c16022101051f060e06070204020721050c100c020304290f07020102011a0604120602070510020703080108060c030103030e030a0f0c06020c09 76
    0x1400c096a15980104d05001c0f01503d06450341015500190440c0306405450100b001c00640100040702400c100060030706085810349600d0354010540c043c000a0200c540001c1500b01d0041c5010f1404000802503c000d03005d10109011038142100c2c000c071240b0080a40c2c43d064541f88901000002c00a0700890600340602c034103002c081503c0b802843c40090007540e00180300c109210100500303000241132030040320512101910024143e0f088201c00c0006446030302050029036980e0f00441c0b6610030a0342c025402d00d451301c82c400c9020848544c0303110301c3c0b00c1b240c03c1080e0101391007030061496034500261140d44111920009085500b20552603040329050541c1196950742c2c40700b240c0403030362074060100c200c4a2508146000b446403410082551207100c0e46082a0001a0082c08103d8000c2e15031200e541c0c0da8241143c1c031a50308444c0900f010b1f50810050000a0080b81d041d48044005001c580c40c588841d6200c003601c1d400c050060b1015210308800b002651b90400c8001800403007542d042d02103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 287671178 1250 287669928 287669951
    0x209041119030c1a09130f0605060715050619080705010f08060906010f0201110d0f0c05041202010f20070807060c0f021c08040308030703050c0901021c05041806050f0301 75
    0xa800c181c01500c00114a810012404d80101c2c01030345c01540b00106034101c41119986176800810356404900f0403582840800522460f102003514209078205191900304150110040010400244610b9000001c80c0c406880c405100c0b4040020b021014010500c2034100750024240b034440c480c0c14400c10022008019054460501030341d0081d8080c00c1c401c6040303900c100240c0c090a9240400d6400c1000401c5c00401520a5005900c1c11581d001003001703440c880000840d118071882c0500d003880c21040c090f020041d44030b14103c840d80c00031071403c10b4032800045203068808400c008a02040d07441003074140515202070108400610480c1044030a000300c40e614014548101d44d8042c0c420850b218031403020061143c0f40011141c1d02c540c8507a13070b8076101e00d080c0c107407038109440120000745040c1c0003c403856070080c116440100140c00800300c0a0480104030840e0000030f0000c1d040000602c0b00144401441402803e000300030400492524100410701481580d50803c052017a0b040802d800701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 287672428 1250 287671178 287671193
    0x105060405131220011e05070507150b0901060c020a05010201051506030405032203050f07030308180109080c07030521040303050c01060b0a0c060b0406080721020904111903 76
    0xb07035164000102c00003c0302e0040261129113000190b0743c0f00408158608002800650080c00151001041945401407041c044022030358111102e101140003002a000032072072903540c4502c094400c030360210301a80301c1c001180f1651070aa002d28007040c108454842180340c1362100c54040e000a200030000f500d001007082c03002c480541d414a02920001000c41d061010620440d01d0b84900b00a4209086406401380d0419080354882558a03026980d000d50440e1070214181c011a5095036645100e510b5038080b1a4540500c0c6801500c0c1d990380c0e00703d420001d40d42c2c0010f07102ca5558040078206182c9181821030a107400c6c2802c640d2030020030506038095000c0308082e182900d8040c64501c4e211203480780d40500510f4070f60480da6480d040841e2001c0c2e125030203508024650310034071003030000c0003402040c0300966045004090307898218640034400e40749044500009111460340c070740440056134000c03510f0030b0300036030301a255a9802e4140d1082c9007003994650602552680c4549002e500d10b444445 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 287673678 1250 287672428 287672461
    0xd0e0a0503160804050307030305031006050a05030a020d0905070e060a0b0403020d06021b1203070e0103090203070b0922050703050c070f0b0402010908160f0503030f03011e0305120901020105060405 87
    0xb1080c1c0e0042040c642400410b005507409000050100d84d0095100d06020707006400c00c582000b000d4043d11030210300c1c2c611690607900800c0c09501e03824255100c841200300a500f00600c040512a034034544800424410803c0e80001c00d0403143d80523413810079034240001c00703540380c0011040420400003040180c0314510002a03168000c0700041e1120b80e07041c00d042404130314210062291103a2444000f030940c0c2b9034000e602817003440d101c0c0c0115200050040d410740e8840e013406076148e004004100b01022615000305040078004001103006404420403042c01c1080d00040800f4030390318404c0100868051142c030340c00c0031403040b1441c102440f030360343d490101101c1280140790b445810b002c1021a4001d078900c01c050070803d02583d1b04280c5246a14900c41030501c1400b0345482811000205c0782404401c40f0b071140407642000789503a01f000c0c440c24801c05208055407890500752000800b013501405250030007c4400500c40d80e4a0100c2c0009094440c041c3c801840b076894102072002c400f450704d4001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 287674928 1250 287673678 287673697
    0x303160f0f0f03121409100f180501140c2809170f0c0907021b03030705010e07080123040f060b090115080a0212131104110d0e0a0503 59
    0xa490221140c40c2284101e00090002402001e0324a40c2a041580005503002c031414105000c001c01d4421100391400c440d000e5032080c0f5036401060911a42c09000e0b007280b140070403028804100714000c0281600440d010701d905075200d95640d007141c9810300750202c841e60881c0301042a81d0400c2182070340680180558142c4003000e640700c0c49a80552401030503000024443e10503404401e0344140b08190b1034244110a40481780201f0003d5051032500a40d0103004180f03e80c0103054001080002294801a41200c141d06200500c11400011000d00501c0311218404010300030f03b500d0b2034645400e5586a140110055404600741c150401c1c001d044249d0081d004200f0b0b00980c0a203040560081c41c400000f1504240701000108111132008001e1083e20f008e69034194071992012002402c17405541e40d48405c507141000815080c802d400c0e04807102c80d01680c03404e810300c65090000303001c0701c3d14139401c1034505031301081e10001c00ca11481002000440320010340003d0795242d4402d5124841c41110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 287676178 1250 287674928 287674943
    0x1410a09090b091914040c090e06010b0d240f0f060201050606090f0d06090b071103030c0912030f0c1005010621050a0e011404020306130308010b0702060f130311030316 74
    0x13010b40c184480d0404070811100c001d00110604050401880245250050200c0142041c0a00750303280700010b440360480795082402c90500701a2004400036001c4107000032109402445031122066041d20920000c29025001016032490804401c40440180c7d2191007503914203400c1158580304c00b01101c2c41034ac821a015820701d09900d0000f40c01c8404030b00c020300200e14140f107602c10840c500034214051291a12814080007858034205d640e07100403201b4500a030341c28040c1c844181405070f001480c094100080c0c0c4d081c070324549441c1100d50083e54101800c0e0307022000c8910284910b10500340035200515101d481d15048051511480c4850502980842e580e1000a80700040c20381c0007933400d00412009010b640407903c40020600c40566041c2d01c64024000410320101d6030720f03104414554143c40b00080b030b80c40d11400d0043d94012610a076005002048041030f003d0200005040f245421000141c0c141d017182081032105040b0351255020b40e00800c160003021406500c1d00020740e0f8402c16 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 287677428 1250 287676178 287676211
    0x30807060e0d020a0213060f140105070b0901020a0e0a06021509011805100b0d12030203070c020a0815060604060905220213030b06040b01410a09090b09 67
    0x10800d00520801c01100000d01801d60307054109640400e400c03000600803200141500700c0010300a0440340c543c030402c402c1c1d0003101c0003009540c2040131900e40820381414000d0510131141c4030f0680f20b440071954016907941c0068101b0145030020344d210203c0009403001c425090902c2c0000c0d664840e0441d450150001900004890b0442500403c92810340c40084800340105460000d40c2d480008004880c01801c10980251909107820945189500044140300f260034424065009601c05491441000047c081110141e250220144001c0c24880c000340001040006104001c0c0d0340641480d10544082004100d11a4031501041c02d54101f22400744035088105c4001d0200c1001c800c0ea0035150380085909402c5540c030441e1002140d01840800b5425038810040104403590005034601203038000054030040f44641d151442c0c110034214544004510300302000152000d1502c40c544c4070440081e040c01e80700d81c05004400101035100040c04500400380c0060000c10005008000c1c4851303283c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 287678678 1250 287677428 287677433
    0x121c0e03031905093909090715091a1c093f0203030105011803050a0303021c06031112070521031e210f04030e030c0406080102030604180b01030807 65
    0x10030205c0e81c0b80c0b664008210082100d805507403850750490035103000702c0d4254035050030f81014802d041c07064081801805006003000c108621603280800000200300c424580480c11304030040310140c0030209011060b49410185000c03411480580540449280c140041580001c000242110503c40b032100d0300008000070036a03002d0804006200300b1000840c2c0a40440326a40100065061310700aa0300c104d002498840921028641440010180d034021000000801d210b64054001010b6552101d15850f00c2d452141040c0c600980081d90b8084004400814034030b88540d9803020660020080c04040b8681000510300704401410380480d600c1c441d0340d4111602d001d104441640d802c1421042451040001c80981a004004100a05006000c25880304e0700100d10082c42000035054001c034607990744c1c0c1c04941c50710310034902d180c2510581d600b0030790b0f40d55035016a03000340076040b00060300d03403400504000584181107541000d01c0004c0507100041900320900701d06480d00128071642d40c0d0301c5031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 287679928 1250 287678678 287678683
    0x90105090702030d110304030306050111060712020d0903020c100320070221010b1003020c030d0b010e0d200609060f030402190b130e01080a14121c0e0303190509 71
    0x1c0d00920220392511005c1722540020401950065000c0d81d000c004e440e48510042d941d00c071400c4080d07101036210300e0004940510640e400403110315048000f41c10701d443d607507020f030a40700b25280440250300990810812130401707942041c41182503141c14040c5000c030040b0100d102501011214800c040081d114055403150300c604840a0920a100300c01909071200c883e0017040c0701c01c1040c0c0f107045404a4100c440388a07000340d81d01150f0400145241c641e14041d40001010900700041c18000c62481d121000c1d91070f000803542090080d0b00c0e980d00b620124489082c6075821b00643ca01c45e00b41800b5031b00c030a4460b0801c1c0d0f050300090444c61540c0e0f46490000580d1710078a483c801804074200d80000c81e0740300303648018202c40c04c0d03021816100c413500c0e9003a0100c0400c0c24029a80c0c0d65100000c0d54002c100903100c11030460a0744411744110031700001404456601004000700031040400000003003000c1b0748103c00d0441d075030901940c210705045444e400c1d80c0203a8800c00480701d4603003002c1016603409 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 287681178 1250 287679928 287679937
    0x20309060a05060a0e1f03050708011a09060f30010f02120412050403020d0305070203370f06060b0a020706050304080307030f021b010f15030b0103080a050c1912050909010509070203 80
    0x6c02500c2d54030664924103503603103046a0040c0d102da5401c100700720b00d00801050500c1407080300104003a00d00c0c1d488000744200101c40c000ea9951000e05200809010006082840018000064000c3d9082d40c01488542950240d24008078218410030070104030303190a03982e642d0030603840311002d0042c00000340d0443e2180150381010b544800440802c40401d07801400810190780300b581590780c090207550301000100b8051200780a4000d060303440c460b0000c0700c5001c40c601113100b1051020fa0000e907031203483c00c65841d50407030749a806000844030842901000110020580e5141661440c03410346c1c6c464030507010292090701810745070301a01880c40b506d501501c458201002c05d203ca0001018130741406000544404201c0b1032074034040c5803c2d00c808140074815aa00090014401d034038687d1030390032691043e800d0000b00901449080781096081c020082420410400e5140b5032070b070ba0500c0c002c080d4002c03d080c0140702040007440c1c019282c4000c0075046510403035404130141c2d20b54400340d08601c203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 287682428 1250 287681178 287681221
    0x30c090b12120a090b21071206030b01060206130515071110060512160b030402030a120903061b1e14071a0702060c071221020309060a05060a0e 63
    0x2894120100071404500035144060351a41c5481c034440d1703581c2011007030744652002000000e4070407990280101074050510380040b500e11b03000700450714541c0c07800201c502503041200d80080e40401013021643c1000000d4009400c00240c0c89010302643d1030b50307a91951000c500090001900000380c40c6400340c09009a01c0070510700b0340e0a50b481c1d400c0004014240b50140c54445c0040a141ca841c0f400b00192599001e124450b249514a051261201c3c2c15000108200e905204100c44e8000040329004243c0502d1030503190641220304500d001c0064962a5010a501d0241840e880004d580e000310100905607203c004104030b040e507038000300c412100a413580f19002c41d00040a104001264640100b20810310128040c1c03a10340c0803013281c984c0c00c00d841c101c49041042c00482c020502c1d41d0540313243d680c441c1c2440000c00003019a82c1e41e0307024901c15542c102a0b401710801034201070502090740d002080c91001c12080c90030200041c0c0c03801460160100029001c0001044031108001d40c40e942c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 287683678 1250 287682428 287682433
    0x1b0504050c0307090f0f0302090c0702030a050304030627151407020d120b0303030106050f04030f0f06050f070f050f0d02040f03030f0503131514040303020903120301030c090b12 78
    0x380c8001c8074003507503000703682e1440041e415240000c1d1400320400c2c42c109503028101c1c080a8945103801b04103042e80b016000703010992041000d81c0040c0d4040180743c1c2d0591160000d15226891820840201c4201da1101c002c0704092022075031854031060803011103507501140e50200020228421001041c240c18219081481300c000c1c0701e1240d03000558070b0038144981e03982640070749140d91303424242d0f41c001c2103180d0958010b000501145000b10701400c0c0040902c0c00b09804c01c1c1d036a403545d542020f4198025107003401429220707024840310340241c640c400d101c2c6940c50318074200fa0f10001c100c045e04030041c00c00c010b0302140d4600030203002d008882020104450035516581c5a408640d5414020b2208601044124004005460048040d00d1250114601000c03040109449820080c002108018400f40d43e0f0544c3d003951141442c029405140290740045c6c403000400c083c14907080200240c2040c4043c140b004000043c042d11422080ea003080c0030104410484601040ca000b50a01031302c00c490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 287684928 1250 287683678 287683681
    0x9050a0c03140c0a0e060105070f08040b03180109121b140319090b091e060703090311040605030c04090c1a031e090c04090c170a020f0405070503041b050405 69
    0x1d8400d1449010000300e0b01030381c200b41c00f00420801203460078490002c408030300c00002219076000780094102280210a181d1103400c150313443c3c081652254000081031040030080c450104507020003824041c04400081203225141d441c6c403004220f900020038104845071160301c01d4845103248941d221a0b210f03a0180b60407201c0c0700ba081d100c0e00010051400c440042c00791100b1140b10f02c0440b012140d904080341d14203d2402e00b8001c2035905400c01504540110312416616141d240081c401140a0740d00d56262504628204510703401d012900d501c1036081040a0166540214a44410b0141110300003908c64040c902074a241d2880e5100301e860007141207410001d6000a0021485807071200205409460480000c040890099402400e6640300c1084c281042c24198002c1540341d0084c1c03196a02d0541d100744c0307500004158140508250858456041181040e03c104459a04202c40070700c91840d01c020020020b0000402c05040c080307129003403e1520741415a4140a0308000e00144501d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 287686178 1250 287684928 287684933
    0x30e030a11030c01020601060816030212070e04060902131e031a07020616082403010606030c0305160e061c0515031e06070f020f010f0606180b0d09050a0c03 69
    0x700c980a024040e0048096103c030a61000c500141a0341ea59146d041ca152503041d42600d11025000001c818907500300482000c003540b580b011440382c0000e5840aa802e110041400140c48103680903000c11030050100030250710b0807044207029203003103940d22a4028018072910003020700703951016009c604d080c01c18000003244200d486200d40715917000c58006494a105c130110060021407220b0008a0300d902141ca00011446952200401c1401074100600142c2c0040e0860720250300c4280465950040d803210300d81c142c01200d034800e2800324100201100c0110152001c4816400b452199400290004102404503081c080d01620b0303800c100618509001124480e9440401651280c031600212040741d051501c0c50807175240f07000d8050111901c0b1108203840700c25150200780158001ca41201c40008000d01c00d405540c0c041680200303044d450103030090000013a05c00115091072010009019a032070b80411294440001c103800280e0070300c50b041182c10101031800040c280100702c2c400101307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 287687428 1250 287686178 287686193
    0x3010807051219150207060c091a09030a0318090903050d0501080f0d0e0d2103060806090d080402040b090411100c110922080a0210020c1504030e030a 66
    0x644009441419001c110a10000e030340d0003030f1004680b101242034001c8400100103401c0f03401da60134104009800d0000642e202c2c001d858448423070328000340d00e00c6400c11280a40003030243c030010000b41c13030170319151104003c640c6988418901a0900600f45d0244a0f001c01501516006040745c90040001d610075103402421540102e8200c0d2145080c8800403030f0303186002c10710f82518884c500080192048480c0107950540f070341d040c40c944c0f000c5100c9544010580f0160b0100803001c0080c403100040b8522107020b812503401d41c00c0300c4600d0b408501082240400040c0c0201c42d500c980c181000742c1c2d40d9920020b800380940d2840b45400c40d10b034006000401404032480500c1480403503410541ca08001002c480090000d0343c040c0c80e60010b10050201410320403c0715401140e612104c00d2015003a1281000560340100c044549600c0040c1e0000c003940d052010040c401640c0b01c0a602d0910b60310a070654807000324151200c110603000200e4109070140c408450440e501a042d00c0e00181e503400e0482c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 287688678 1250 287687428 287687443
    0x3070506010b071208070e0405180a060207021c03080106110102191701090c0c140715120b0306010b040b0306011e09080c0a0510140918040210020703051c0203040308030108 76
    0xc640e032031200c0342d2030f4005000c1e1a40e20322426141e1f0702c0d4101080da070400c0001500001c0d0001c01c40c102049040c0f04503140a0108030805801483c015a95180a10601c54050440c0b0400e6860f00200c580110001e540003d6072411191a4540783c0c401200e072070080d600902c60b019072840400e400001a10340d59030045003055005c0c6541d648007030a41e0340c80007048144c8482c001402c00141480c0d600d100000c1a1818100d011140030084510309512000205014078104100f80c002c901c807203550000d000d05501a040028100740d0240406500d041c00e0102140101d0049201500002c00020240d909c900c0d030112405c00c0600c0c0040001541d0f44016000303003410300074030025014601c084411800c0c1800b02c01c007221006003084c141c090b08514100d9010141d00d810100c8c200c01040301560664031b25107003010202c18200644a203091a10410030301001102c90f620540d04011810000b1641c08158690b0701044404850050b684101c1d04900b94400e44d0030080ca106008030011550348400503104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 287689928 1250 287688678 287688683
    0x705150103150e0105060307170c04060605070b010803071203020d0e06010f080712080403060506060d09080310090504050c0f0120010509010b01051804110d05130203010b1008060f010203070506010b07 88
    0x4002021403d00d0b01c600703075101124800d030142d104800400c508001289030300e0004140700c00b0398040031005c100203000e5601551013000064070104004082c010b039102c0c1d0724010a6288005d40c64001141c1d1900803509a10600d0001e0550100b99101d42130740a8000090030b02411040c0e030080d40c1c4030f685000906500d405540744511943e070001c00c0c1020045041030205400624080c2001d14664421020700001803556800041c10300201c0560052030042d030050074880c0c048103441741f030180b080c2c0503400d21540c0600011410f043c244070110301d021444441051040d24001c46103101400144c3c0d4440c69050343c8070a10007020108121a0411360105001d105c262000380301500c680d1004503890300038801035416041c008460031402c0d00d0a503003c41e44400c60b13440002d08042c0c0c1c0310314a90403920300f165140f5a042c08940f41c00110f180c20311600041540844000c112018030601c024030034140102101d0055280d11211000c40c0c0c000c00c10388420755808421244550b8503610505503a8000d81000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 287691178 1250 287689928 287689931
    0x307110609070e0609040c080a2001170631050114101205070e12060609061906030b03030f030403170a052e05060409230417070515010315 61
    0x32603801c500c00b040100480c1c490580842642d2184002c2040c4c900c0e01600032a8401c0d041d100000710880107020900905004130f4181d030840030b0300484100c0300400303804042d040010b42107808551100c500c0714183c0080c010f46103401000e8035005070049400941d102e84011850191222828403004e40186060f950740c0c2d268040101d044030140311000421b5000c5034040307a4122501041e4030420b502c00c507403000365490900310040c004408610141c0103009014140c1d040038040140074200018001c2d000303102900c000e140f00e00ca0203000a0248428000e90041603120105550180d40070000c0e1030700c0d0105100441e54905042c5000b44c0400d10418618030b00a01030000282ea080851041a21a0f066120a0a0081c01400c00100305d6048052040500c00340c03404040358940303545015001414a003000000c04803080d41a4500982080c0144c0d51828906400c21001941740a1400c45030100d11500c540c44480170719003d41400b80010061500300201c1000000b40503044480301003614907005e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 287692428 1250 287691178 287691181
    0x120d06050f060c030712020a1203061e0b09060a050f0d0e100506060702010813050601082503050a02010503100312031407020f21040e0f010302030705100e0613050603071106 76
    0x340b0540c0c2c00307441050609034005006003004aa0020b60a0b840f0702610710569941041541d14400da6842421070440000d90b510740a021000030440d14606d59810003140081062400d80480c00da07101b0300e400c1a01a80340801d40203d103d009509035420b80c0001034003980c8400407004140024241900881c51304c1c426034242031403102c01d601c2018028140038214511f00003054005558411000e005815140c24920f00c15001c2001070251178040c14810700500901c1ca01c8401c00f54555082a001c2080d019000900308000380380003407407041c0541d0a09010b52282d4508000040c4007003164006402103c00303400070710fa00d40d4540e0003000b000c05500d81d880ca458503075010807a03640b240c100f640300b039550011800f0712028017040901141c559444110900e8151101c2c040c50b08400156425071500d01c50324010b00c00c5240c02d220348006014140d80030486a1030462000701031140d0225107500415000413038100245040c10301402501c0043e04c007030356034109100c000782842c000c00c4580001e0b015410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 287693678 1250 287692428 287692459
    0xc0303141b2a0c0f0d1e0804051309060e03133606030506070509030a020405060f1e030705060f0a0302030709051215060307061706030a02090f0f090d050706020903120d0605 76
    0x1704880c039402003c04c1d00b07580c00b12016169601c0700c1d40070540344c42c001884000b885544080c50042c0b082e65100d0302091450382c520344182aa26032001c910300b00c0d00140a103121408071100342c0c0c01150b8404152581c00001c030200c0c0e04024064003002c800681c40c0b9500e090503c0c000da0000700440e4410b00499080740d0710540221080d0080440456054001070703590000761030203800ca207420000003082d10070454005400184614000d2400c0a0030036543c080c0c0c0203c81c035043c03141400412050b41d15038548032520240e0f003c1c0d0311079030800005141c1d011001c110820b21402000000d04005464900001c1d04405413942c0c407044e0041601c1e40f1000030b400150388d4140401c10324200e403500c0c0ca80251803a919450f2a040c010700030001501403044041c81400340c1d0361020303018044c00c0300b0784100c115410030520344100048010301c8810503510250030185a554044201c44845130000c40068585d01c11200180c10a402d011149a9920340420000da595030300340e01840803603504450501c080e001c40c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 287694928 1250 287693678 287693689
    0x30309060f050403080409090c0506041e0515031f0302061206040f06030b062202031e090c010219050f0f06010824060d0f080403030c0303141b2a0c0f 66
    0x1e010052120343c05010407c054280341c1c00418003a4070602d280002c854480c004a600c075017007076118007007442000488a807040400c0290101501c415907002d501c00051b184050150f100c043e1082146a04080d010312142c14244e494502440e4000e042c20f569090320700c4565200e0074241c42081c419890125272050180700e91103100116a805a0304100c83d5844d0000c108201013038840381c441e862000c0c0302c2c606480c0d03081d04c000c611800c04a600c80d6202d02081144441801d00180300203000d0b402207070102ca080c0c0c0c00040030f4441c0400c1d01600480010305d4a8582e0400c641701c80b46e0409441500303000450401c01040030340c1600c05200031982d03407129202102d0150004107040b40c056030106008201541000020120514000c10140068031074035541c40d00d40780d0080d48160000f851031101c0c00c041541c9409040c1814001669034812402d003103180500c0c0356003061700c44100341c03400107050180c01039049144003420303034052074007010083c0d18010f1526141a159898401d440180d8152000d1405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 287696178 1250 287694928 287694937
    0x105070515090304031a04050c01051206040c030f021315022407030902060c210403031b1e03050309010f02270f0a0306090212030903250f030309060f05 67
    0x110041403a400180c1012000078005050b0440c580010403010011a2604406180c0c51030707010960300d09071415042050070243c0d0400800d040100030400380d070036401010308940c0c0210bc2120005194440d4860603030060000000c0401c606001186901d941c01408040b40200c0b0b41a100e01812112889000c80e1925440313004508030016100b40400b590040031000b9501418504000036801c0b01c680028200760003018002500d94003501c82540c1d0480304030102032081840b040c5503801c060440d540600840c240c10700382d860901901c081d00044c001c0350341075071f0742c0040d44e800c800d108101d00d801c0080603603100701d464803003d600f40000148911984c2c4201d420031840340c00701040c0e004081d40e542544a8249150a0b44100d200360120581e58900d000100203611860300080c2243c007610610418130340003288224079070000e0001d0201a100410100c0310340b4011902c10031009142425181032803915000007a000072000d0010007016000040c44c1c040c1d86094603200d000440900c0d013203869200707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 287697428 1250 287696178 287696183
    0x306050f03070911090306100f060309020117060a0905160816020d05030c12131a0402011b06020f04030303020c1b0105120c0c0a150605030a0b010e060612070302030114010507 77
    0x8001420043c060055100e1800d1034501c1e10424a0701620f032000a18200041e07407284018017424504002c404410001e1383c000b081e03a42010300504110342c00103483c034010810094104a030031000a0b0b400d690750f0300000c01a2001403010400b505002d00c0280003a25140c07001808214000c01042207409040803010030329516600522254400030303c201c81030f40001e0501000341009002114650003c08402c51061400d81104408d008c0c00b0305002074a10700404400c10321400a01c24000580d0b440070b80b003100d40c50700d051102003509061920320000d20900b082d1070140d04012602100300b5506030001c20b03e021175035080780e040000280b860f150502c6820040c5011038002c03c0014034070205290078551100c2c0390140282441108030300c407402c004807480201c0e14840004c00b940f0b66540c0a10070f040140c0010303802804e02c00005d0761b92040c04035044c0207200386010a2000160350765540c40840d000b010481e42c07034240904007600040c1c003a40081c0550b003287d40011801d101c0c2c0b54454010380d007200343c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 287698678 1250 287697428 287697433
    0x30605060d0221040f020f12060a05071206030f060b06031e040f06090516090e0a06021b120319090203060708070e0d0b100b0f07030e0a17010902010306050f03 70
    0x107080241000254840e40c040c00c00150769a03010324000c06506400d92165000e0f0040b00040580c910400a910707000e401118410405804030b104902c1000800c203901c00700c1488009100d40311680140c0c0c075124030310241d04200341441c1c00842003044045464000600c20041030181d24074510403c011400300712079010302150481d02e2034061740d81050340950001d0081500c03003950184c0b13032659400c1d561000f10603a00c640c0315009950400645400850003403007224010410750704180819900d03400143c401174469900440c500321f8407903a40021101d1a0060700803108515041c1400096603007044031442e40510011055444402043c000c1c4039019070300402a00f8255280700060b1550340340900078008000340380e8040c122644980425109682c0030304c040110034500144075100e50f08083c0c01c207000a0b030060003c040b4030503248040d90182d951500b441e0341c1016050010500c56162684009021b41907400341c01c400b2a03041d40a64a143d000703076024800030352558240481d80300501503260701513 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 287699928 1250 287698678 287698687
    0x1503060e092a0a030204060e090f01051b0f0f03010f0906080a110909010e0105010914060d020d0311030903010501090b100804150903030204030501050a060608100812030603010e0a05030a0f03060506 87
    0xa03560b4001c80304000d90001d2803640d03c552030742c01040c221400e03a00711381754a8201d181400340c0141d04119088081580800030b00040c500001e070003081ca814401041822040811001c018648000c103850441031501000c1e80c0300d695640d0490704c2032134a4400c8011140ca8450049405030000c11545d4090340c10180d0360481c41c2e6040140106030302c3c000c0c03803074055561314400c030325a040b400c3c000d02c4e00030400e01c40c1c0416800440894812100d001420091090b11055010b00050320b0700c4205003005905402c00490100501c281541103100303004146038907520b04000462071502c070381d0000c00c403130740203481c40aa4000d4200c8141c407030381780954015244180303042514110801c5500316215a074803a20300035080681d0f81c2d0b0b8407030070340d40199035100b105500c440081c840507a12006441d1300900341d120800e2414900002030361540da0200c88034800340f20000c0002c0c800e44003504503044024909084071000912401c044d0f46a0300090380c103100140b0404e1044020900c64010101994030040809140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 287701178 1250 287699928 287699983
    0x50c030909090f07090605011107050a1203020a0b09060f011508061009030605180607080c07020607060b1f02010b0a0f1206110c011a0d0b1f1503060e09 67
    0x1032020041c02942c00384551680b003001d00e07009000310380c010030440101166482c142000501041c981900562059000800c108403a58890b110a004c840c2c61600b624010300311820100d080c0704884002620700c081d4202403044054000804602c100c0949200c514141d80780c9041c100030080c00348851000031406001b10703003a441c0050122290004c0f506000c01803035601d994240c15101c040300c0341461020300c40c000501c6044184403203984424139140040d0349103022044a880380c081e140e0007170300903500400c0c2a02004416880048030713030300040410790108040100b0112000c040c05102c0015420400022140c2c14805030300c82c140c1d009800d0403600d0508061510482999140303003680d40c0c54441c0ca5500540031990001c0006100600010490180d000b0b50308404c900c0710121a0701079040c114050000c00c044480842d000083c54042031800180002d0140000910780c02c001c402821404140311a0745d0198801400c4a4103900f03880b540307030399040859841c1c8124603508036502c103071101e01064 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 287702428 1250 287701178 287701189
    0x3170a09050d200f06040606050d0b130f0606090b0406080105060307092003070504030303051501120c09230a0b030705040b0c1f0c030f150501030b010e06070c0f06050c0309 76
    0x11030403280c103d80000482415458901040c48001a0742900302906100038031040e801200d010786416a2001038030714890784c030080b1a0710700609900e2881241e00802c82042050f40030b01c80141d400140602c8801d446a0340440102407529040344281c0c501500010850810b014a51103100c00901600c0505c0c680403400002d40805040042d1240b580c823040b004c24030000c0c01850207140710355100c0780c03600c3c03c41c680501160f20142443e401a0b100b00098100c81e80d10807075905501700c9000e03002c10301144600c0140c511411039048401e55011104400c00e0540604840707506003041200c0c1400f4950781c800c80016544400d5400c140052400c120a01580c4400802802600c80e001e0807a010f208000785a005111521011585820f0f15074074a040d040d81e1600400654a8802c00200034585003910703c440101040d2140505043d05c03010f1180b0745a0060507540c0900c040a48096501c1c1014900801c5441142c000c09560040700394011804c1c078413803016140301030f448100075072a1482ca50308100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 287703678 1250 287702428 287702447
    0xb011d06130803070b09010204080c0d020d050d08150a0b121f06020706030b060c0c010e0604092a0f02031210030f05010b030106050111120a03060e0403170a09050d 72
    0x94200204001c0300280c0c904201054009042c284065911288286880040880d01030080c1089070b00500043c09803100100300414151001c50302c2c4a1a410f0520110f41c11201ea1000034007140a0342c00c0c445001c40d04041003521401c86c0282c5028a511030104020b03400e0240d015000d05204c041c40b49064a10b51403900d5034000c110855103c4494242041c180e40021441d0407100041e04840c204022440d054010079064010440d840c83c10300804929140d84c50841505081c1001850030383c021540d16800c049034040c0484a40a2001e0a080042e15603060700300416016100d214010b1078890600c2180c201303c0b1010590301661500319880c9070007039503a201502c2d4a00c2c14403040d40000005d0141140f1050b014441da001003401000081054219006548030906208000300d002c02401000300c0c80103d00941d00c0c06060700d46444000443c020065034000400803034444081c0414580c00a1460041b41c0c64000301d40d82c1542ca10f00e807a026034440c2c0c50010501c0d8090b40000c0da40b540126030b240c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 287704928 1250 287703678 287703737
    0x100f0f1a0c0a081809010b070213020d0207111201060501090b070812040501090203070e060a1703220e061c03050d0e070f0e0f010311060a030924050a0b01 68
    0x2035061a200080050500442400c21100d4110000300711101124040d50041031580c21519610158985000c01c4c850380f081e00402441100360303030f49100d003840855040d5054508030030400c6403600601c1c50814103598100b01428405d84404408186800d014001c0c1c41c02d507401a562070a1045c90300d1040c81098110002c221a945414800c000c514004004568400c901640000c15a10340314018581030020f071340c010444514002041051548804100c0c00440314005040351b00540c2c0c0020745410341c001e40c940c8602100c8644911165541006448400d03110a0510dc0c03220761100c60403c408101c1c2c03644070041910140000e040441c0c000c1c0007404060501c2030300824414086130643c2c1c20200c1c00c0d0010308180034994810b20180d0699803520b64041c60110040c400b55065481c1c0441d03042881c00b02521544000560310811880f17500040e007125404a1202103010034040b4448041409902040541d807501001480d9034560b030107890700c11813041e181d05203a025031006c6000c00d40d0201540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 287706178 1250 287704928 287704979
    0x3070b070f020411030619060f0c061814060106110a060507050d0f050702070e09060a090812010605041719060f020403021309061b0e0d2306100f0f 65
    0x1600c0542c4880c0544600682c4c8030903090756920349081085510703c03c0d040303141443c1d40e020a050050607042a88101591403904101c50042c10a10b0080064615090003001c116480500c42d0100607090340e070255030a85082c00d85000760b813240021600300b2490b2000c2c146030b5000000c080c02040082e444580c0000700ea18020b4a03140d42450700200742c0d400105510035056843c1d0400c0280b942c140074800140280c4441922681054642c190313807094050028810b5035924404041046450802c0700c403030b20301e072034031241c0c0c29a950200a01185c129100d43c1d10141c2c113000a41c80121400304104408210281c801c4074003841d81d80303440c0f0080407507481440762030390308200200c0903a440c440035032a00d40d20074a000c112013010b494010f05842e541d048400130000d180074540705180d0001940200c00c4ca09645d6030383c58000c0c6090605000b075038401c2c4410201c5100744d80951110001c10020321501850401d6014207603140d8600480e07180702d201c0c2c0b07505950000300502407020440014002d610704e1120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 287707428 1250 287706178 287706203
    0x6010e0714030405100b0301020f09100e0d060605210a060c050c070305071a030609010b030a020d0603050604050715050406030209040f0212010e062e032706050a0b03070b07 76
    0x4918490b030300c00d0300d05883d554480841c0741d44ea40e0083c02000720800c416002075003030a800c600648054002c040050b4828020000e0804020b8803480d40040000303c0242214040155400c00700c00a014134010f0314002d44101c2d000110502c5000d40c5021442c01c0c15001f0101c603207103915940b004140ca00d451000300030b4200803112a00784100440c2c8003540c010405015054600702210b043c900d28403080306000d0700140100f03c6280d803058801070464144441c100da50359119130012000348189180c98a18074506040401800f01c006417151080303115404449199454044a100030b402d245946000600100030030300c0716601c20703001f40070458809400890512041c140250603a04190800c01460800d8401003001c3d079844218140c1002054800c002108400042d2081807107120101249080b45003d0400f40d07a4403c0c0d108500c291b8080094190f04100558442c5944000c00d10555000b401c140108186098600c5074400f501001001002d41d180340004045480e08108801d0b2140c181c150b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 287708678 1250 287707428 287707457
    0x6060503030d06170607051b0327030f0f03180607060911092a070305070c03030224090d0810030c0f03031704020d031107050607122006010e07 63
    0xd02940c04030b5100110700b0310708000101c0007410040c20311030215800070f01031042d03c81e00003003291440004a103100d42c110407007910a610f54458021f10301d1041d00d500743d440040311040d42d20500c002a08a080e50000001c2482c00c9035100c81e440f28801907034104002906603002205ca00140241010b40154248171158a034503080380c1c19940c0c107440ec2c2200c400c10f2a082c9c9018080e42d60310401070403c40c030000b44000d000b008251111401c0aa20f000001780c45c00c00d0500602c15122003c2e4003202600e4901c0e12460029102c0c51092400303951546100c0e200f1504458070003c41f4880c080b100300400381d0907080c65084802c260302611042c502c1d420380e400030001c02c0c000400b14001d08400c99040381620309c0c6180040042c98100d54110210a90505100040c2c0d102020961416014500009003594014800c1d007008011351001da440072002070380c0810000d003092818446c503a551900d10803480d10b00a18030405800c1c480c1a15150003040040c88140c0e0241d42003a0890417900c1c24055144041c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 287709928 1250 287708678 287708683
    0x329040b030105040812010b160b060a050409141002040e0408070201210c020705100806090402010504120f0c0e1603020f0409050c03040b0c09060f3a0506010201050114040906060503 80
    0x641302510301100c00120560054082210680140b8801c055a4900340c594019106050a54803005280d05030701d40100b200c0d581c3d241d6014010303040041080101441c140b40c00d5500c0010224900c0140c050030211300384104043c800e603001c89041e401004400e0340c4594645034a680403100490600c442d01d103400300680c10510038001c8010180d200024000342d180c1001e40361494560081c2d20902c4410000c180041d40001441d8001000382c90103211a1210320040e03905008135000381012421303190007178090000380e07140903c89a008041d090001a00d81c0405601c803082210b6012842d140151540c80c0c0d603200740d00030460701035a8030200d810300e0f0301d90300d00c0c02c1600d806458150032410044103010134043c0302483e0981180030030740824070300a98000851000c0c0a24154000c0700c0741c000c60010400c045005905410f02040500d80c0401d00c036000140c591540d5800c00408294640000a10b05500501c5503905071048225050003a007401400c06c8060550110300702c40e1240c039107000040ea520704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 287711178 1250 287709928 287709931
    0x34121a1303180915080c030c010909050601020a02060d141005010e061606090308041406070806060703090347040f020301021e0307020f01060b07021203040803190f0329040b030105 79
    0x20031344800702c124500403800d413401c0800710b0203601c6504801c0741c002260b0782190f2550308641120324042156960880141d00b0040c44140c0a0b401020010303c41180d1402d41c0c0c04605080c11765010411a17407034803942001084140e024841c0820b003038030f8501c0100d00d05000a01507440c514000001603d882c2d03941c00d0709842c0c0e40c400403404140d5070b0040c40100011180381d040800e810a008204070f00e040c1038004c041c1007015041c3c90150400158100c2850311a04060010b1604052601c0c542c90440030601c1c2c2d9080c90b081808040c416a50501c0707901200900f4203041a0300d0300445c0300842c0c42e10385034014545650070049034190340c2001501e240c2c086a04a00045e012015060768507441c03c0c542c040e00f03062250030627000503491b11509014040d082000c1d40c80341a01036038048030f440c80e00a0090320f14880c9420207200d611021680c0705809504808040c00b40750240d8401004c0c183d000d109038181c0e400119442c3c551407040d1100700070001418442d12a200c4014000b203405480840401e0840d00e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 287712428 1250 287711178 287711201
    0x80306030f0f100f090506040201110f012307050c030319060503150f0105032103040609142b0c03030b0105131202041d34121a13031809 60
    0x11140d43c030b100c102c045200301d107031002c4012018400c1c4030700341e501c1c02c1d2101402080241440b0002d1018150208200008170b101d008a2000300903443c80000303c1c003032010320300320b40400d01d904400000300b03082e01c41c1042d51580400744000754110744ce008612080d0320039032000c041c2e07503550b502800612950b00b0006890200c011400500e2a030410007891141020141c00403802640312600c80004824160404044001d041ea841500c98407503182a001500501c00c0140281240f0905816400004107020341c0c1624924052075010184909002503001300c25802804607016080c00404240680c100d0303100c00605141c11032800c4a1b404402152141030380000600c0c01e14607a412085007400d101d007881c9a005081046035802403610001d641e41c503a060305401c0040c0c0301048032030176800003201d030707242d0300240c09071940c002d413100804164440c45110a54108140220501071030409100c00c40c0102d00324202d01c0310703482654405584c04c28041c549050505810342002407034400354400c8058500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 287713678 1250 287712428 287712433
    0x607032102190206060316030303020d14040506090c04230a06030503031501020f070e040f050c0a150e010306030201090b0a051b0f100b0a1a09041b1106040b04080306030f0f 76
    0x100440013071900d10300801c101d000754000842c880c1404017004070202101d6140c40d000d0b035203030f030842c8080d03000e00018910703007412240e994240f0040140c0854200c1c802d803800c00440c1c0d4505215400c22082d10700310703400750000c0c010303940180c1c0c41403035406466540003200700ca02042a036580c2c0d0340c1c246580d20450b4074038004000001751180940e0b0510100d4000c000c040000d16406080c400c1c40695031002400003400f804007002c003201004401d200500040d44020039419503996200b40c90a41c485111b0501800581000c51005466000c5c3c1310b18000d072a01030359040d207400d05100399949140d002d0b000309428410280702c04804108411074006014040001034240c00d403114a4080c50000c0040260680500308207690b2200e86407a14950100d0f0889198014500d0076841803224501c500c4041c983c0060408440045021300741c41103140010b0b15688507602d94044c12989602c504040d54000c103098019404500807404010103075402c458000d090f60701005001c02c51324600040c4031140c100301c1c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 287714928 1250 287713678 287713717
    0x9010e0115080118052e052704022205040503040504060e010e1612180c051203030a0c2714060a020c040905120f0c0c040b0607032102 59
    0x40c10901c451454418842c108040207504060480081c0300e500041e0b0b0b12010b640d9000540442e0407501c101c20305985140250314080b10aa00b0070303056161a00600d8042d542080308105218103203400300d080c0110301403506031140ca50342d00300071581c4118107031100740c1c0d00907031030b8101e040865100e06400b0318807030b00056030703907510b860240001c2e0b81460348810001d03001c00d0010410340d403504242c503034455030311440c42c0c04400a0311405d8584000640a00880510f001001d80e15174200b2203400001c14010021903001c0359a5a0400021107001d1180120360740040c4041100344140340c0000b1841c1816080c401329400c90200b030001c03c01103402c1c90080c010000d030f10810038040e19810b0030030040c0c070175150307140b42007602c0802944e01c00b00b0014190089944558841c07c1c40018414400007101d501c900b203981d100c80300100a240d40049000c12558058004240c6c00d0345054803c074103807404040c05140c100603950300c0580d03481c59030034500d8414402030100000c0c102807a1006107000c0100c80d0708840030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 287716178 1250 287714928 287714939
    0x260d110319180b0907030c08010209130e0d050702040608010c020307030305010e04030503061012020a030207020306010801020421031b0317070206072106030c03030e03120304020d030309020301020909010e01 91
    0x540c46901d03003141605107003075458010341d03128184928489800680c0000c103501c442110b41d1400c0940c0d84050440c401014010400f01e0064000307000b8040c040360030345200010304140400b20f44c100714030b5600380d40c0b100c01c0050300d0702d02540103000007500003040040e0035aa210902d5080d500310300710760300060300300161500c01c040d058850980908a503184040b41444e1943c5c02030038509c4043c000500c544c400780d103000c01c1c0901c125000320081c0d01e0a98150346034468000d0260281d00b0207901248a4051100082140c1005100b594101c540d6140d0351040040070400c030084107034503503000341e00b000002803080504d1040c5a00055034540310383d0350000010303030349907000304107031400350030103045400000503c081c66a000381410046100c3c000c4100081040696410040c00d403a1320003070140211100010a150300045401e40700101035081e02c469808180c0040c91f0b0344803c40e4002d500104014026010911075071011542d144007900062904c03415500241030f5140c240d11008002d0142e2006028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 287717428 1250 287716178 287716201
    0x609050702062e0e0a02160311150c0406051b011103060a090e06070e0a0512030c01110406090b030403030b09040f020a090c0504030b040f171305060403260d1103 71
    0x1040c0071484807000c0f2803800800b400700e0744201c00444c001c0c01c000c94054003c5a04032a4542c540c1d0a42c0341c0b41e80102d10b40549102d140018078070403802800c0003403203a803800004461281c44610700e00d42c50641028415105604082c59135404001900b110a080140900c1141c0004140780e0341c5075203d140030810003080c1c825981040c1d0784d03070741880c110300c20311780d000107420340c01000c1c9090040c90200204042041c802c020b41c401540000240282c05000c04040000d05907000b07240700a021041c48000081e00c984500c1c401c07680014000f4400700100c1c41240c0c041d43d0410303c686400314080e951312001907904942030f5401d4a070301013005000011480c044d02c01c20700130f00c0c5809040c0041032003c0e2001c1c1a9000324800030b840341559400050800103009405035600380c2c00b40141c00d5200343c10300869015084080b00d00d1011542e210003084030310348078040e9401c50394024003071700c00d14000c0e40c500a818603100000d450442000e000f07201803903400f409015541c1d00000951501d0f460105420758 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 287718678 1250 287717428 287717461
    0x130b0f040f0905042001020d03090510140603010b12030715060f0303050c0606190e06031c020f06060d120e0d080a051809011203050f07050106030606180e06070e04060905070206 78
    0x41c0a081178000e121040c1d80100d0b01c00c1d403e410600340040c3d4080c050030304a00f08510f032a255001185491410901580e03200700700350140c0400d400804c10360200100b0b000011604902811181d40240003072400520400400300024864900204480e0b54400510028020702c1d00304802060000c91782006a00c801c200150f0710a03001c4503400c184002016101d8842d42040c041c2c1c3c10340340404000128503441c20040b1809113600c80c242c04c4445200d910000b9203984d0130894503000c41c0514008561240740914a01e00c9107508803056601c045410349058074131020701a401500302c0142101c007000f00d00f00101030030142407a521010f585802010a4001100c49103141c24820020310300180000340349030548091003903160400d650748034940c401d4081036000305500103080b50300304840442000761a400c02c40454400d498804c18115103462000305494450194205941c0b00600207504e4034442c00e14010075031800b503c0001c55035240c140241c1500c104803840f001503840007007801111200c201512 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 287719928 1250 287718678 287718713
    0xd0608061305151006030e01060509010605041502070e07050d150b0a09060237080301180b0405130b0711060421021c030b120f070603050c130b0f040f090504 69
    0xf0042c902d4600c06032815070702240a894105030307480c01a1080704e4001d42c023400282000801010b560341c1c0d0750748000c1c81540b1901903010040d90f0035001703241c054000105c00041e00d1284a45c20003030383d1843c0048a0a0304004d929000c1180c88a02c2072000005d419018006080022111651080400c8000c0c2034203c0c503070301c0b0340c0455101c4d00758070f8804400201c0240a52100103601f0721840c03054000555504070200d405804281c1c00000020340006031890358035203420a031800d0000e9062203040008940086510f5100c03e020740818800082003071540503070000c110b00b494140517000704450b91a05a085504440300643e04408c03002c181c0501f00c800303490808520061402e140254600a0785a030000400c00c145900c0d110750403000d03561303404031043c460640c8084810915540f54403a84d1202107103d20000319242c50042406d035051003084403060108101100003480c5403807101600e6602116007c0c50480090001090442c80c0200b4076004025a0001080c43c3c1003504010440c1034040022 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 287721178 1250 287719928 287719963
    0x1202070b070b04052509050112200307170c1906050d0b0a0b070321020324060705011b080a0c09170a0204050c07060b0301150b0d0608061305 62
    0x10441004000120340340c0c0c035444070030700106071214600603280c05001501d8105d0034542d03c0e010b00e0124405400c2404442882e03106101c5030340c0c0d41c00d02203c2800b198102070406084000c168030300550b000890740c6a00d40c06012a441e40750303203840d05881109101d030140c1b00e9410143e410b00382d80c6040304002c0c0000b0611200010382614107040905688101c8040d20059520b506c5200c00303e41d284048000141158024540e0701c00d0140780050505200c3d42d1000300d01248400350616120461003503d00c03840c10102c1b407159410301c0044c1002851040e02d40980e0044e4200140c01c0054402c0c0180803054915401e0240c85c0c0b104048042c118050003000000c00a15007480010190b5011003040119006a010343c0810040d0784806c501700040840041d40280c180001c0c840040c010b0380040406500542c0c0c00c00841103514101800c2c0c40e9040320090008040c0117003400040312075001083d505c0004940000c4059491a1440c00c10380200e9403680103070750100940c0c1c288402031121041c80302800d01c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 287722428 1250 287721178 287721193
    0x8010609050f040b100819060513020105040512010f0f02130909030903022815030b060412030806060c0d03050708060306061f1101060807030302010c020f030403060b0d0b0906041202 80
    0x28420b00c6840100080c01c590504030216611040a010500203001074034251603010403006414010341c02400011140305d07140c0300018491524200a40040a5059555034a0300e440e00c0104584010003807004909035584a0100410200358480c0200c103440300880035858103041402030f020402c1c03990010340400e04011507400041e901c00003100c25254100c0f217200c100341c08900300300c000c1c000c3c1c6006100052448400440d2980401b400c1108664040e5810312103640502c4c2400745602480c444c08680c1c090b01c500600c0080c4c0a4034243d80e010750b000d071015040c81500e84243e403034040c461481c080401d58403030074402055400109140c2c00740c8150002d0009050420119110b01c405100307081c00014000f24240031503100e40030100c80034100800038410310342c50304000740c6c403140c032407008034059803a0450310162540003054401d03010b1070000186082a24548803a80076014030030046034031420945840c0d000454900240d4081c109000c002c200380e07e06440c090800d0b8401c04159001e5500501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 287723678 1250 287722428 287722441
    0x120b06010207030305030402061614060105030c030304060918020910090503070f08100e0f100b180907090e12030a0507090f0f060c05070504092105030c1909090c05040801060905 78
    0x1121f0b001603060b0f40d900d40d00d0310120f8001c2043c0352180402000065010b0410034800c070002003190685e103048069500310a8844109690307442079102d8034021420301841041030311034200e02003d0300502d080c00986040d5030000002d9608010b00c80c10f0f004581c00d40818001810100b0441000e4607495500144e4030b414004030580d240d81d070780c004404198a0b503242d1001100280480541c0c040c001c42120710008200b0406409800c0301400e00703000c1d960024004100c0140301c1c1e2a18012010b40001d080500c0c10100c005000e401ca080850700d0500c40e000702c90200b100b07204021031041140d190000f40320704101d000202019010390181f0305202c410316062051404101604040310610b04064030034460724a400c9081400d140c0c0400c1e401440c00044c8001d101b141016512030300030004401000d1601e0103020360740360005550800c0e800364207101c41c403410300312242e4100e100c84941c14051400c83d0390700b4a0405558075031901d4000a000840c042204032002d0040038080c2103460414805481c0c0350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 287724928 1250 287723678 287723687
    0x20a0f0e0903042d050405131505040803010302120c1f08150a09020d09050a05010605120f1c0c060501091e020f0915130b03060a0e0405060601050c010b060301120b060102070303 78
    0x225180481325103003c0146410802d990100703000f07003c00b4000740290319203d00511040c8044100903030f0b2600109580400703040e10791161034030852313000e4151401c5074219001e010345900140d41480003840740420005056403186035503203c903038491000079030340c81000301d00030700b0180c2c05450b4050480059154030229610301d80304006694194100581340c890001c0900090301640e500a413081c003849030b41d00280103041d0405ca080c0da0041c0d40641d0035001300280582c0c0c0d0006250b202882d608070a602100180a049a01c4011078a602c0d041216100a40f10001200e0003a44206810f81c0d5800b0441c0501c3c01450000b1010f030400482181060540d4540c0403c43c45250380c02d034404d510f03011285a40c032002c0416604001c004445a00550341c860003040c499034010b42e81e2521032000704000160b104076a5200303034403e50380280070b040c01c2d40f1000700544842d000384003444415501ca08143c025621100c0141d4000d100c8900701c0e00d0649183d0500c104402c0d805017003039045401044081c00400d400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 287726178 1250 287724928 287724959
    0x6050d0b180a020a030809090708160503070e030d08071101090525150503041704080a170c0a0c0306050f060904030e040b060301031b140d020d050703020a0f0e090304 73
    0x19036101c5400c40519909141003440001d0020341c040f94080e4040113100a000207000d00c5071050b01d141d2416240d44409440ca407108444d42600c0e0030403102030107140ca100700041c1d6000111810440c0310550010300283c2441400d00c5c0c8100018500000c01c08416030140c0c4290f409103403003008104107450358503400d0711490030018045181c2007240c0c0c481310410031598110f008000c6403144003580c9440302c0006100b07502c199400d80f2803528022501d100040342d00221400c80701d00b10b0007444041e1180c5d8409544500f0340d40030078038078a8140b1620040d007409204800c0d040d40b00b040e1515585085141c448104d680280412414210701e004006c550f461707807820305400a030142400340403c0c007444006400343c501820002c3e04060017000000c100801c1181c110400e058146085803069210080c1e6112501c9412540c1c0d071001440c180040542024290b0906030b0b0700038000e0707840850700d98020462089180d40b211030f000c04040b2042100206009020b82c000c0c0154014515241c54850900c205c1001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 287727428 1250 287726178 287726191
    0x210a061a0912070b07030815030309010e1e03010c030605010210150b070c032f01080c0d020c07030209010e0403090e0601020d031d1e12030f01090e0a05011503030306050d0b 76
    0x82c15201800509070400c9940c0040c001140300c1c2e9642c01d201c0c50002c1c5080d170140d5040080a90071048030100340f5011080c0c408805041c0e5a0f00b44210b401c0701048155840c0560f1200c0108603001c2d042200e450070b000e801e441d1252031302c0c0800c45501c1e0800091400251410300b40406180c0031a0f51b42003400800178200b02c41704902e106803180802d00740410100d400d68002040c2e8010400848502c202c030360071292242e802c8405090600c2102c00043d6902242141c0c40f404c18102040a6490140d007a80a0201c00910004550f59107441e0341c04181d0f4183c0a07040050641816800c00080541c004400005400c51107120956400c03c080042c0d601d0131000c40d60014543c034ad103003030380302e41c1c200c148291141c2801d00121003121103040d1106240a840901c2e542c2d0b00d000350300c0000c15442d0940c08503405020340c52100c6030349030f03e40410303c0001c00c0c119065132103d000e0441c10034085942406100caa0303400c00e80e07894108e146145000b40840701c051340400e014104075a824030200e0340e41c032040340c0d0082 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 287728678 1250 287727428 287727439
    0x190204050915060d020c070e06041a0613090501080a140d0503010e04020d120e0111010b0f150c060703050907050d0b0403030507140a110d0327030302210a061a09 71
    0x80c55640020341034021604c2502d1101d1010555100000700000c44804441c0001e6100e4140c2d11181d040c4010f8840b8049840f04140a50582c12041e0514a00902464042d003a030b0002d1151120a02415140280e1185140e5070180b1042801c0c0888a01c02c0342a500c0b1100003041c0007e2611806800c5d40014411106103907400b07400903056407150000c0c0795402d2340c41250040e0400d107403039000d0072800703a10300c1250005480e02102961400c0510170740302421401003000e1101045a82041030141a8403c2c032416108144003401e09131904200d203d0081c10701e505d0105961070400b2209140410562200e4869014158a10042560788071140d410603090310380404c030395075100016100910014208003464800080c00314450f43e1240c0021b0007070f1900815a4812584108d08038181c0f00c0c1c40e10b0851120300840700b500b91948540244881aa101c0d0802504102d0103082f054410500034403182005607000e41000381c0d6420b244240b2002e041c44c40d8542190404507007466036540504031445020340d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 287729928 1250 287728678 287728711
    0x7020319030c0605041401050a06260304090509031e12150f030607110105060f01080123030607090608091b0f0109081b1002031e22060201051902040509 67
    0x242c45809001c482c150001001d1040342400c0c07070001800310000349140e2465113000046401040380d030060404482a10b4004044182c1210b0069100f200310116030215100030040005c6071610760243c107120350796071400780d51511000c110010050015003050001d05008218540c0048141e040a6401c40092040f1381c0480070310f2804103c0c03c032200e00301b01e6418442c15080204d803581c420700c540906c0070700704000e12981d16004103005c0e5214484100c0e034089030300f02c80180b00034088104165080e202501941d02c81000c408003003414000305136061400038060f10014020980c2041000d03030081c407810000c181e01103460341c0a941c04091503801c42d00c11007000c52100c038903a10910703a01c00500150b03015a80380c03410800762010342500c502206070003094005851642540007005841310f02081c40c502451007214030014030010b9005008031800250800d040c02400c0c4070448040e009894507400010303040c10f01c0702462141c500800d0090440a004010500c44c0f501c0e88944030f50050003a140b1409403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 287731178 1250 287729928 287729933
    0x20030403050409020c24180105010b0301030305030403090906080616020316060c0306090f09060c021b04020703110f0d1e1407030203070803040b100b03040f0f030e04020a020601170307020319 84
    0x46c0f040071824521400f00e0060f145816110b078003649801100e40d4004400e460288110742c609030b0b1001d03c80d403c42e202040c401080820301410095512a00c0303441d0481101d40c9440004049400c55008541e85074452070402a01a250284640c4c82186600040d07040c003100e0110022103810300d03040146502e84035814420340324025084607001d4210031000f40100f0140110000052040c804113490007410f0404449401d400403038007c0400c62800000c4601c11100d005110207580f04030800c0701000102c00d041c0207840002d1194410100c2c510703000c0c1620750040400100840ca40748603000101181c012460340032034010b8082129800c20310310031521401c680c00c050313045014407000604400000804c1104100421038420312868401c0074100340c00f9101c407483e0b60715000444006000741c0140c194000450302225074070340540e22034541182d00c2820500400c2c2030b07809c000e001a01623030001c40148905115407140008411840c0011340c03e000d46a0002030f52064005940c4c4103070002000c20307505 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 287732428 1250 287731178 287731183
    0x4050d11010e01020d1a090f0103140a0c150806010f05070303051005032b0201330302040c05072006120c131202010e0a03320d0320030403050409020c 66
    0x2042c0004004c64568120203007070009000410b94100400c10074606e170714401d1400d40c40241c014145041040700b41d80c2141e0319141800010079100400f40315601c94040083c140c0840c00000d0001445c0100c038520300300402412103000a0246810b02071003100313142d26aa03014058840d800c0e0989004a1540c07903403003803840100d412381c10158050040d5045012092000441e05d01d4111400360503c030750245144049080350b1004481c01c0b81c40410b152018004c00d500412903040c00304605400d103140d581c0350f0006003200c01903680100400c03c04180a0103011014000c445400754000b4040c0d00d524540000400030701c10207100000988004002c100b44080000c191444070780d000c12a800e1258030303248015200026280105d001a108440c0c82000f400d0802c241001c4a42c8039900342c49505100c105a00c2616881500071400e00245607402d020000401a5280b01010343e240001d4208601001c2c02c0b1200d010400c0c030305841d804005200020350300c1011103044403400e220041c5c892111101407070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 287733678 1250 287732428 287732441
    0x80604110f0f0415050417011401091a03010f05061c080a03230a06260a1511030a0b040513050c0d0f02031c091401120203060114030a05010501140304050d1101 70
    0x152038010441c40c4e400b426000030041040c0c5200c6100104d86030f41601070741d42603500c045c41d903881060a8000420043d04190403802c074003101c1d4503011507101e901d5004a0b084810041c50840c9281c2c444081c41034908062600d03161058240c1003501d02e2000a4031446110700c40d400070719040558444040c0c4110035200020075484003c80c420b5807003400d000382c00101a04880c010405d101020501e1102e2003c1c12813032180c4541c840ea4040c08000754186c84a0b04100003040002d0021606c0741001d0011b806040020342c810b410400001070190010000d01003103850081850b04081c0c2d025001c400400c81c00a1030216001c0216440a41d074129850000e04204045800a4040c491024448980340d001344040e4152511561a0070600783d40c0d81d01003070340b621a11081d03408907040450111b0714481580041d6400403042c1041c2c10341030041c1f415051260b00886005082e203079144014001036030f0241010a48494184850342141416102d2035204d030707041203100302030060308172443c41c1841e0b0039003099 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 287734928 1250 287733678 287733689
    0x503011e0b0307080a0b01082203090b070501021b07120807030311070501020304060b01050301061d0d05070608040c060c0804090c18140f090103031e0507051b01080604110f0f04 78
    0x102d40302c0c10700d5100984801e030113030b500001e00c5041185082165104185041c4200d0440e07c00d230701c00304000340d0f008443d4070100b0350a80c2042705096002c941c10b4400b400522109118a00043e542d034a0b202c60707148241c10001e000803150f001300c1c0c0e04000010381094000c0585d60070400c00351380c448452409800406000d026954224000726148080c0441136010714030480c09244144185420800112011721007406017102180407441a81940780c00000c1e100101c2c0c00141002e807601e4041c0d00d860340780070950751001000900d00c1040004110070780070910020002824040341000e01ca0b59518401d00075030184204072170365228000403051094092400f440880c46003000c080d074990743c4032040d0070015641c1d0390040101c0d40b2042075a080030710106040701c0e0540d43741e811003c00d281d2a26280408803000d4000c000040c000e542c08a881403042c102a09030340e540d82420000b10b080051700b4210700034006407045150442d401c0b14100800b0442e80005c40c0d015540d6910822403004d42480c0c003858000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 287736178 1250 287734928 287734949
    0x1107060806040507020a03080a020d15090e1911130f06090203090f12030f1906060302090f0301020a140f1605101b020703240e0616020d0503011e 64
    0x8416400141190003540152810300041e07440410907039407021548030003800110008001501098a0386c0036000102c1901008108000001e0310113121503956003101482c2680c81c1e90101d035210042016200d032981ca000c80c0e211800e00c50319802c0725042c40c005140d01412840107695101a0302d40e0002d118110705110800c2007503201d8003c14000d4004a40e171941902c2060f100e2403002e840001e9070248590a55019441c55131007040c0032540032000340c20007149200c810403101091070b0310b000d540e000d800c669600680718580c007401c0081c0100c2d2440340c02c5c087c0e4810418002810381c0072140080001d40c1404569480800c0004010039218101c1c500c800451310014030b00402c44040b640c504078419010080c400d040c18042d1080c05900b1081581d00940d0001d40104005050179600310752030051100601d00450641140f0707001c1d00e0707141e14822843d0300b02c0310030409614044010004601c550f0310080403511401c00300a00310b4071042c011001222211200d0300002c0c05400d11140203440391001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 287737428 1250 287736178 287736193
    0x6050301090c0302270a02090a38030c0304060b03100218040f061d04030e0a0914010e010b180f030d020d0e090403050a03151a07061b05091011 63
    0x400c20b0310141c00e404100c0c424038076a4441a4482410900156030a00e02003d24080380c440340c030844000d40c4040d40304c42d041001c005c400a0840c104019460150487c118018250100b4010707204c03445c0580c042840000301c041c000d11019180c0d20042e03c1c1d0195000900007410f00380e0710002890b00943c800305011807130000400c0000c0c00710100c908803580c6005d80d018058001c1200740d00040c5e691038024400072a602c0d00090515030b000d602e6503600207019050920214000c8000304015441c1600841c0c203071900c9041e81d040800080d6805030040001d00300b5101ea65050083c100f20310300c01c17541510640d0440303802c80000c540e40d151034a003860400404460801280480180d102c000711800c5d840401c1050021012900300389443c03520480e4159503051500111030000d074000c10b10048000c3e2505c400c090b0225251540400800c1114640c3d14015100c0556113825010781d602052078000700d2050340c603c0a0b83d6030b004000d50f000003a040342ca82082e05101c00e02152455044405009c191007001c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 287738678 1250 287737428 287737433
    0x90a0c060f0908120f18040504060b0319020f01140c0109050606100906050f16060f0e280b1e0c0304020a060302030f0711070302040203010308030a05011d190605030109 74
    0x810022546080d0b100c51400e070f80d68204040e1103500703c0340c0c5a249036400b00688501c400c0358000904028101e070f49628204181c1d01e0100c0d00300d1b03c00301c030100d85503699065424172605c1e080140808901d004829100b0292250740424002a01c0e4039105050144000702031554408880030340d4210811800200800031003030400310f540742002d0320094028a00c104503116614070620011098405945505142040081035091700340c0c4180d02c0b210b090380020881d880003c43c0340c0144031408580c50340c0419544d4401d0303402c5082041440219201841080041c036844d40102c850b1b03903445400404e000415076884500d1a6010498002c00ca4075960000801040300048009580a0350003510303c0d0006c1c5440e4403007a000c80c0f0003590f4400f42d1038054400500c1c2280304a030060500c02d9a6030940b8013803079882d0f0209090b07804c02c0e081118000000f1040080030f0701144241030040c100d810b206540f04096082d5400301d0580941408041d0b08842d0402e14100f91039002400141800b4008000500490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 287739928 1250 287738678 287738687
    0x8271203160215072004060501050f040b130b12010906050109050906090603150a050906060a061704050309041109040b0307150f1803050d080a11090103020c01060905010605070c060207030812090a0c06 88
    0x40420700c110702e401c07c00b0078039522407010785018103007150140d4541414042c0c3c802040c1c001c44507080d0320784400507020902000400180c141c0725480c46160038294107100d0860261000303500b2039410007108034810852070b40e419108039000784080e0350b03050543c1c4403d400300e4104046c20b01540c100741c1c104c00130b001d001319541d48801d1003060741c003003500c0517502c0391420410010101e100f40000590726001c4808500a04e204058000f44184216440d001d13004003c1801e403920900b01454031080440c2c80c1003182464066042c94031412070203049a5420544403c000300c1d15083c8800401c0451203074110031902480081d14078a0020352500c82041c0da82c5410f603540c410070340d9007100007a400404900c43c2070035801790800710015010711a0608490100440007034001d00c2405100b036490341e000103404400d51061034040c101c244c1d2032643d5480681820010100282e010904561110004001181c21103080d00d88401c41d1102c0c0310310688070813002614102c0a428040e01040502000040c106d401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 287741178 1250 287739928 287739983
    0x102010e03120a022218051302091305060a0c110109120f03140a050702010c02070e180109140307030f02031c020d0b12100605040b030304030f0827120316021507 71
    0x1445144e1041c260030703086c14030654005680c0c5645020041f111100146041441140d00500c000d004032950801501e80c1460107105071503d004007a5584000300b0b499600580001c140150320000b404000e440c1e0b500d400a81c0c4d80311095404000024541c1e164980c0301c1d4001d030b100401202c401045c14280441448020300c000e48181002d0761030505100c6240703001241c40d00803680c0e40c828007000b0341d44292a100516004c4940c20500b556a42e00c0e200020714400440b4100b440c02d4402551650788918028103e502c2e144130035019544144000c181c1600c0807030034400d01c4a81d01c0750143e25250011101009406401c03015584104070f1034085643c5c1100050002460903d90000d0092a07642d809100490f840394000a805070810442800030580410040b07a44601c034461191500c80c61448071a01b0501104402c1081c60282c121980a4581110340480b0810340101a514149810046001030103108600901451500c00555142d541190599440746c1d00008405c00010104100d1140c0c21301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 287742428 1250 287741178 287741189
    0x7080c07150e0406090e0706122307090503070b031b0d0207032c130203040305090d0b0609010f0605160213180b0a05040f0813050604080607030b0102010e03120a0222 73
    0x5072410018178070071036024802e2085541d001034189203040c01c008842000d0510070b00d95041d522446482046184620114a07480c0e90b0400c540150400d81d038000c00070b20700c3c0d41c4194440c0d07109000a202c500500c9084076003020601d881d90580c00c50000c00c04800c0e000b540015201d15101003055020f00d50000406d440400b24a09502c0034140001c0c940c00350210040c0300700340c02c0300e0b411882039605449a401150030602a042c4603050003003110001d07032150742d48882260410180f034203001d02402e0464400b4050400c00e03031141c1c400c90801c08020b005001d90908185484950b491039025500c6004020015002800e420300078044d00402c01001c11100b80c0b0b00311074a11a070000210200302c01c4c4a007600951b400a003880607100346480e510708a80080d104e120f0341d02d0307040c50001915070382c000050008041c4003004d000c1c2403801040c086c0450f00b91099084c15641041c0e4851040703d004022a460000942c88494135a01c982d10424000d005584038240c22407181417104000f40c0384c61401030304844 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 287743678 1250 287742428 287742431
    0x10801050702060105011d0108060406050a0329040f0b1009022d031501110f0a1416060806060a0504081905060c040b03010306090201020c0d03050a030b030f0307080c07150e04 77
    0x245ea8100441d6400c0409410904205540c2c0342044258454002280c00c02002000402c2003500d0307000280e8180700b1903208403080c0341410359030244820080c852020000030100d404100e03291640346c84418400c00c407402000d0141110001e82190050344500000e05083c0d10115100e0ba1b49074612103a103020441c0100d40b11034040011044883c43d40200c03823055041d405c0346004c850040d0010348202580c000c12160500941000c500c0e000c7c001c1104441250040180c24182003005141c542000d225007034606e10f0b0a03c901051100355000300e800c07a0440d0042c2c491907991406d0020450b6031f0302030b40d0441c095601074050400c5c100200c0024159150b805801501e21a844140ba0984d281c4110301c0f031080013910500041002c1220303a400300310810f006005079401c821030000000d040303202c9034804174042040461280c0e04203605100d0006080c00a800902c2650800c414160f500d0144001c002c104202c00903000c11405014000700000384140e0407a0706082d8011440940082481c80b001809203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 287744928 1250 287743678 287743681
    0x5210a050f0f160e07121406040605030a021e010504090509030306150301062102040305061305070515300f04030f030501180c1808160603050915040c0e01080105070206 74
    0x407408105000c4440501d1020f0603494138007842d41c0c0350ba0100802c4101840198600c0401c5202540241010001002c1681a25152a0080204a580c190411402540301e0301650005840709101d5600c07014480490f2110502e200c0012034152042c1d4112503e810b00b00b0040c800446800005580100070840f4906441c100c24005c0c82c1e043d0000348112000031700701110030074405111040c1e8580d8140e500b0b2001d850542c507519108d1a12206540742a100100000340387e00307116040c060328028100c11204442c02402450754822107000744050486000c140410840802c40d140d0107038400440f0f407200003005842d01e0030214101c440121030a5000c11402c5803100b148038400c0c0329043c1a20241e44a042c0c080c0603484880c4020120304000074188000f12514001d03583c03088610100034084130000b884070b40d4403d5026003200f0003660000301450f0031310741444500180801d074242c1400600e500c01e1417955641c140400e6412142d40044500c04c911000407400c00c6064107e00d1040c1c0c0c1d95022910036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 287746178 1250 287744928 287744953
    0xc0d02010504170702190e180c010c061d070303050c0d02010c14071b12061104061e120f02032a0a0e120304060816090f05210a050f 58
    0x20781c1c4080701c005240120744015104028542c0c005020010300103400140e20901204000e984580ca0390009407195404038100f00d500c1d50902c2c41e10068440041c0500400d680210010308000140c840c002c4c00ba503102c0000c441500d00010096000340d001c44126003225650b820301070141d500c8102d1510103802040c0a86054900500038481c4211040d44c42c0a040075048a0200c015084002d00f02c52030301c075901c03001c4003c1d220132010340082c1c1140201c0c1c403d03190041c40d0240458070000312500c04510144030412074582c1000c409406200e001d0303c1419407042010302101c202d1011030b503913803266103481c0c1070001e844c6103076000e903101d8034148503203055a100700c01c650b40c100340c085044140703845410002140710f00c2c07146401d140e00c0d540c06060400c1010200c0e11807811604560000d2000440000410038014001020034855200904145540608058450903100020300a1a00640030101ca0700710700b00200c00f41010080008095410000e081c1c50700d65165225031611240c10b1046400c1003c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 287747428 1250 287746178 287746181
    0x60509150f03010303050c19030e0a08010506030a110a150e040c021c050a0207050a081612050a240213090e0102090901031407121401110f030708190e030c0d0201 71
    0x11400d0700040c0441c1584c2c0b85641c01c4489510402042c2d0642c0605c0481000c1460110103400046120381c9405051984140601503e1602d139403018420368100014000c403030301c001c16824041034110303000c03d04029404000c6069800c00354414054030240303101a000c5180d20000d41d83c2c0240c012501406a09500b98080f83c1d181c0b10082024019060408510801401a4000c11416800380162526035984500003800c03500250301102107500300b0442c160095034900381030009048030003034000f201c904580b207440e0390b10f03603142009290304841c108101000ca00c4c0320310001d410114481c00d540e15440740d50360101c01a140c7c404c01501c41d090803103203411440c040c002d49010f07447c0500482180da04e9500c07000311038925080b8488880c040c0400c00300d003d501d404e05882485010703502c040d50601c40c50742640e00b1625040100c17105503000380602c0c5090580403044079080481442c0ca0712050716208044502008054807034552070b450300c4040c3c0c0c0d801c0d9010020300341c17905050003510100d1003440f83c10790 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 287748678 1250 287747428 287747437
    0x21801030b061e040c05070c0501030912050c01271505243f03030f010303030f0e07080f070906030c05011d13090b0604060305031602041506050915 65
    0x40203044920700196007401d060041d440d1860140c0300c4041002c1000c0081800c885e207544004000886c00600d101c04d12140c0301244008190038a410003012516031509002000c1066010040020004030413031b82c84000d400aa10f03444103918a4074100304114200304c0182401c08045400812181c4c00c0c4c0c80008041c8a034034842d081c0d41c01f881258130100c58101449a0350b0491407580705c40d074180d41911900300d80144411078281040c2d106c01900006815008002c13005200c130200d40d0081007080310b0421106010790441c2c2d030600b004903020040c003c203030000d404d18602448a510803600009200c40c0d00088a07940c842c003c0c030580314210b40b00c0c04440c2c00c0e02c0c411b01000d441b12003008410405544501a00c071000b0100c0c99448410000c45d40010341038880c83c0745c1c1858200d480d403c01e0024018201022a0031040843e01000002d14503a5626128000c403100019100c11116141c2c042d91a150458007035040e1190140114a84903600540990403000d012401542d00d0280e8454105140c01204e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 287749928 1250 287748678 287748683
    0xe19060b040923070c05070e07050405090c04230f09040303021c0b0a06050f12090703030f170109110c010203010b03090607050403030207090b0a270c050a0e0f010207080706020102030402180103 85
    0x28456a41c600c0810340390300c035030b11008584038401d507c00040d1101035400100d00584090b55459521890704040250141012b13011804203182048200460700c0280c0081d161070460034060015002000d00207080c13262101b84032071b0040040800c001c04c061f41940206640c400b000004500c4046140406085645c1c0210783d94020840c0c070002d0050310300800150450142140e10755182000c0c4040320540b6810548030082c0c1e42d130000d0828001c0507008508000800030343c1c901110086a8580004040001882955034640e55400c24814280405c41280e4881c10302800030356503540d46280d04001c5500c01c80740c00c401c40c01980d0101346010300c03941c201e0f411240c1640c0104142803c2c842804010013560300015800280c1c0c510006884c0c22461800b00843c0c0c11706c880303108640b42ca5801c48107540e50120511b003005000c01c010028680c100064050441040d00e10444040c18000141d00e091110740040c40b152141420010720141d05400841c400e80c42520302c2014250800c1080401c0002030000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 287751178 1250 287749928 287749991
    0x516090b2808030a0c02010e0114030a0504020402091c0c05030d0504060e0d020409030c1b0807030303020306040b0301021902070e0411100c0b090312011d010e19060b0409 75
    0x55206030001e4802036900344080c04000c40300341d80d4419051a580c040c402e084007042c2072000007019581c00045000f540d010a082100d542c60041e0054074580c44010554400565036002081c06d5485540c1500c004201c041c1c10b0b2001c030441400075002c8542c003040100c802500c2ea500c0410b4500700420701d004c2074030b4981c4466003843c0c01c081c3c06440c200100981517400240601040025a40d54004c517855540a503e0380181e8078254108100c0d0f6904044c0080059024006d04104101c00010b1060403242c06190050b182e480d07900006000d0014160265415800031503116030500f10310302d04544888844e002c03900c50f40d984558546000700b0848000e085548003195200d0384e8145203580b245251518904040030f80b40b55a14501c41401c10342d00d0a05c1036002151840e507000d080c5409a0240c40c2d141880c5128001c0c07403201d25020f00341400703030030100c10022002c6000302025520f203055420300d80c00c00f8061a61a005032040f00c1c0c0041c0f180a0440c4d0a120b10305003210741181f942015450769018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 287752428 1250 287751178 287751199
    0x307200309030c060c0c060d0c02060a0902032a0406090c1d030712050f0d02100f02041202010c0804210308240f01090e0f07020c03120304031412040516090b 69
    0x201301c5643c011015021050159020b5002c2d0395440307400410742101c214200040e10a40380400074a00304000b13182d458034038900181c840140e0780c0002d40d0f0069208042e0384019070b052030b18041c83c0025082e4205900241070020202d40e4100d50b400ca8840c030500c955490003003801e5042d140012a102c0c0b684a501b5400001040c0035003da46801750300038601460840c5c100c0b0302c00d0084189031490403240f54005811100703640c00c008002d4003c03114070382c043da1000e40c2020708292404604c80800308000341407040c03c2c080c03041009501c00a4400030b2110302d0100040300c69260b1400c0840212a1040f00081c03031140001304a860815010389a100100c452000d04496070700034003041445030100103041c003c600f200016400380000c03600d481507402c091910441e007400b44010749072168801030305120b80c006e40c40b101010b145402c00e130780e4003a8061500280840302014000300300c1c031a048a03401004885810801407000010f6030124150b1011081d59100b0b503116102011101181440e0346e0000c85042d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 287753678 1250 287752428 287752453
    0x604080d0506060403080a02010527070b09120f010b030d1d0108040204020d18120207030b15010c080409021305040614060309030d1e060b0a08010920030720030903 72
    0x1e021a030720040107015245869140e8860401d2900711601940050f0344070b10401c926015603c2500d810f075079905848440c014511508152240c900d40240c001c00b031800300d4054011355071141998000c0403448150342e6608000c840c0c1502034103180c00c9803030180c03040012007000a80300d902171413403002c0000c3c44c61410303003071002c0110f48404c0003810580c3d10580900c14191900c006103e2044008a0700726840610040fa00d007012003411210300010664000a000b040495142d60407198000c1505071701d50001c050a10050710861168040606801c202007000310780a4440e500800f1510112051080c41d40d030344000304401d84c1e105000d003e0100d140003d60031440c1c201303500650f4004800400303030380c1400703440300601c0c0440700114102d0142880420b8040c5011180740b02d0b000141c51a004407601e4044405c5020700f4080c1c041c82110545a51040d558441c100d0400d4803000d880f00c4c0c1d0f00c00e242e807420501380080403a902803000030f1164100c11711501d004030f07000048545902024002c0c01d079164601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 287754928 1250 287753678 287753681
    0x19080f0303061804030917031806070f0209090f0a20030706050d150819030f03151401121b18140d080c070603020316020d090306200412060e0604080d 66
    0x5413045080c04180d02000c90300c0d8020601d18a075800d61038000756100d40d0540c0482c1451b401e905021401250100403c41c0840d080d0407011300c00c560140d030403048a0301c0740740400e85400401c282c0c1422034042c254401d42003022030051040194258000c100000142208140d00c8800c0303403040c00003140c01041001c0c10300ca00c9801035400409100e2480e0220b641e07c40415040403103003031000207540342600035941016040000c80c0070040b1149820171844202040b040c44509080c0200300741c42c1000c10449a40381e1013009070b4907003416100014859203000c12001101440c003d4074140209504c003940fa1140c68105c150002192040d01741d06c2501108074007803011042030400242d50801c01005007241c3c0d50740030805030005180b030355001692031078400c0d009048a43d2400090085400079614000816446210041030704c2c5c1060780018100f941052480028242d984400c020311004100000e00c100c030f500160303400078018001404070108141903a038036542e040b90024008102440002c0c0072500c203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 287756178 1250 287754928 287754931
    0x106050c060412020c0d08040614120c18030a0302060402010f050c06190b120a1b0b0319020918010306110f1902100609020d06050f010f120b19080f03030618 69
    0xb0380c01a01c4180b2445c601140c0d807404401025500004000303400c200032980700c50a01408050649140d050000c590a0100c4401c0c2c040c2c82c81070800c00c00308071448102c221030700700081b0210080c12602a1020f070728000e521030314102c40903400f04a200d00c8003503049014100b19840803405d040541055900c1c0305a00e50000302002e2135050640c3c3c0c800900216072202d40d100401c2c001c50600030000c8210b11315004103030890b1100401c403e031400315001c00000603a5020740303811402144880301c1c034185040b890070090180b1243c450348100c21710307803844030040c803403e4003030580340116000d01000c1e44e46c150007403161064045018440404200c004045e6401d9541d1040404142c030507228404002000c0d60251507070f13600841d1000380d00080c01040b6100510507840104000d40358a400b200c019000a00b40010208548091054000c0704400e207039690303404084c101d0741c020041400303110360007000301d071041060258034044e2050381c0c500d040d00000041502e10400c0024144444080643d004010b0700741c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 287757428 1250 287756178 287756213
    0x7080c100c081e1206101b17130501170f070c05031c050105040b010314070c05010212040f0c082b0219030e030709180602030603071208120106050c0604 67
    0x1480640031405600c150301c045070380d00300f086540382d95003d00e001c011503002601491040c8610303079820100a8001c2c00581000c1411041041c030b0025508264040c2450303082d8040c8400d07400244044120749220640c0280c0b07600381d94036034003400c080b120000c2140b8181d600840c02d200590000b10480e200d02d2401c1421440f0f2402d90b805c0800724890084050b01420150703187c40e84030710051202d800c0c1441051840340342480c050000c20a00400d410104001074003041c10440c00c001030109100003501103440c5410120002e03a0545014180804c40380c02ca00310845d521240c0303041c0000c0301800001c00d0805411180c6100c40000a0a01003403c454492210442036003d6450310300000c968110520400c0c030b020f0384580c0d50150501d4100350031b00b47c0036000000901d24082e4070a0203444450403460113164070000046c0d9a40343d45001030311f41025070703005050207400c0131118010004007901402040b5000c214000699880300400d50b880d000f4210401800e42c003210006000c5800003211000011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 287758678 1250 287757428 287757443
    0x4090207051507020d11030a09090b030a0510150e01080601060503041a041a01080d0207030602091903030e03060601030b03060a0902040e0d0c140a020a0324060e0907080c100c 77
    0x42d050392071200003440c22940360001d40c002010318044550404d0314400b9005010b0702562400f00e040e04060f040c0e2005006072107405507210f004144c4d0b03803400c00911008035080411100c168203201702c2c41c0003600d0074580203004054406c03000981c2c80a0b0381c114506a4070008082e044c140e00b407400c1203c41d034000810030780e400742c4c0d07290020728000e42403100030b8050340c02070004c882000c400614410700001d0682c4140003507032000ca40000e94981c08640c6606580d4443c1c0096620100c0b0342c0020f0700702c035010f0340304003801d40c007030b00700008150b04003941c40c1c006081034041c0c40c1c0700d42e030700d000640c03c94816140c0150550001000100d0004403584000d04443c4002d000040d104040003034146403074590f00c801400f06084005449c1401100f01694403800210002800700490540c08591614411b00c0001d05402017100304d40c1c0d149000142b01486c54118500c02c000007996041250340c261815500d10995010f04500401e9105002c907131a0301400c00503240c00d10070503180d141203401c60207140c03060b240c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 287759928 1250 287758678 287758693
    0xc06030a0903091d0f060901050a03111f0906030c0201050708070e0301060b0a020c2107031b08010f1a09010311060a0306030206070b06030d081b030a090c0306020a091a0409020705 79
    0x1310041c6210481c10140c100384040700b490304007041080380c440135264501c03401e50400104400e0f940c0d00409010b803503002034100103145070031000c00c1c040007041307042076060102c0c2220f285a803a800078007a02110002d540611001c500d50005a080b40c3c015a00c1c000060710070381c0000d03c0e881c017800741030750f03000c0707014000143c095070700d0b608a18213810008800005030400052511540b030801040001400301036800c40072a009280d11a0760780b0801c0c400203211000c000c01101d401e848100075200100800002030040062400c0440e005102040701000f005090741c10001e000c0c00e0505915042c1c0c0e90004940040401007c02c200440d00304007203550815898485c0800180c0310980a0b100310791040c6514040c50410408141c285140d41e4099403c00106404000075100c074040d11001850000b246035940e0344854480e200076111002d00600f1076903d0309000402c02905034002d0200100e01d58800f40c040c0d032a62036121154410013070388250142c2c184002c2c860040203074000d10300702e4401c80c100c3ea01c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 287761178 1250 287759928 287759939
    0x51902120a060b1206090606010804030c0b1009061d0a3206032e180203190b060102070303170a1e02040e1803072301090b0610020c06030a090309 64
    0x42a0300000e00b00d40b11070302e518010880d4100308581c50f0350380c1000700c00781180349411101d80c1c0d41d5560040c03601c0c0c1000304410108040c1401451780000c516080600c0040380c0c903022071000111446403150030b00d09498440001204800012550009240f43d040e8038500e840c2d100c3c05002602c1e0f100c006015529540d004103000b01c05441010b1000c002000c5401d50500d805003c25003803001000ca040c0b040502074036000e0103030852040302d44001031542d000003410b0b600401c01c000b907030050b00e80082d0184200c40c14241e0080800052141c402d115001050b40343d56500012a10b4a4041c803008020802400d02c0c1034620035007141c0151302481035613001444107513031a100d60042241490481c06c45900090078040270920010f401c1e40110a44990072107540030441d80c2e5a43e01c43d00d0000703400c51448a01f858004440c0d49401b0b0208501c0b54003d11541c0000c2c02e0503004040c05803880c13417040f20345c010b819100a0010800524900e00108001e06590b03c00030f503940641390800d000c13010040c80c924003007007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 287762428 1250 287761178 287761183
    0x30501060c140f16180204030c03080c01110f0318012c012a031104120210090503010f1a0f0a03120c050313180b03030a03021c0504060504051905190212 67
    0x268601300000400c20340b407130410f0070001050070700303411007455004000070300c0416208441c50084036404601d160356450300b420300e140142031100b49012800000514410f14080581c003460044a90f40c0ca44903001582903000c0c0d00300c0d90340f075030484d641c88415a0700082029404e440029210060b0740089058194204a503126074003d0b0001c0c41c0740d030080341d00c100501d80d16224031000e1080c5d82c880f1074a00f030300700044a01c1c49400da010082c421104002410806031194024100502d0094020f0116030600c0f02070030701070306082000e07020407920400301e100d89162012241c280540040c00328906c4509540300c4c1000c0d8002c0303000d501d0034001c846a40c0000a18100300405483c0720404510031901c0c244400400c0d9102d55a4200010f5810450340e4902980c1c00705c11500f40340741c2400c00607a030b45043c45942c00e4080700700700610051071a110030030040c010070384c20052081d07100b0011f88890083e00351003000c40350a912406800e0f903005c6400f01c0c4000d0050031012543c0c9000824180b80308548424961 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 287763678 1250 287762428 287762443
    0xc150c0f0d0f020607080c09060a020a0c0b0301210809120a0c0618060f020706050a0201060506030103051b060a0206040609030e0607051c09060806100e0d030519030501060c140f 78
    0x4000980442c02e07014000d505002c9a034000c085880e01c20041e08111082c690300c3d000303240d1200d1144c0d23000600d02d0b4805000f00b0001104507841804100380d030b940d402030301200d41c0092252100a8060030020341c0f84d80710400824020690000005080094540900541424104c01704803244100504a00410500102900245125607036001e51065041c1e0904030007405500401c24444140400390350583c000c18860145c501504d0540d0b01c0d0310407aa0100c1c0900247da00880d001400080003000f0b00c007000c0b62400600d40308405ca04c550350014001c0c01185d2151400340001a0030100110300090095040f00d0022402850110a540c42040000d000d55001d50001c440a60000011842c840680d1940709841400380c1000413580d4035003c0068000b40c0018050391003010b80100c800c00e042d000720801e00321a4400351041064548910b806005a8404944403a014243e2481e400542c0d109000f881e068400f259a58110218207540e03d0b03142807155285080940541d685403030000340d0810800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 287764928 1250 287763678 287763703
    0x1021e030429071803020f040c030612060911030c0a18270201020c0919050c0f0403030c030201050a05130b07020f0d030605090a02040b120a1107110906030c150c0f 72
    0x40070038140524013074180030020700f241c1c190001030b00c030130005aa200d001c0421010029280410f41c00c0d4545400c80062007a904400c0d6600b034034600c40c00901c21242d100d2421288601c100c204000140d004240ea9644036082056100003245800c0c8603a4048ce2103c96580a00003001301d91000b0064964105900340035a1140b01c403800040001075607410001c806100310103030340c210300904100d40030f2400401801c2c940340700380d61500c0c0410001180d04040361008400c6203080c1e0348036505d0b031334000e04001c89900d080d4019800c050100b46c084c21944980e07400344206110b003849806c1283d44041c01018014051401c1d400b4404110100641c10301c42d80c41410321705e81e030014905041400f040030003440681000c610f644180000d004003003480d1b08881020301203c0180e07005503984d0f0070133030103420220601c40d00110041001c800b0444690340c00880710700122402a015500c01c1c3c1030595468140d420a0782c0051208480344a130b80171080103040e94640d035010380b401107e49901c40703840d1640f0b45524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 287766178 1250 287764928 287765003
    0x3110d080402030105100e06040209120a06060e011e1208070c0b041701020f030103060504170706020d060b180f0f06031503120a020d052b06050102070801021e0304 72
    0x1c0200314035083c0b283c2c0c3d900040c2d9501e1000c00500304150b0084854004080a028560000d540a450f0392000d441d001524048801c482c1c1d00040c0d071034000003800c041d02c00e0b111b111040b10004520981107207803c03807000203815840702d0742034a8150307440005032580500783d801a408100b40c00208401081c1c0501414000c01c0780f0b560349181001c01c40f28003452002d00c0f01030764414040c104a04a8000480e411260860b40209003600c0324200f28000390b5000783c45102550002403c902000801e8024102c04465150304205407503854203104002c0c0b00d5580030701c8091102c02500e20329450041c4442c803100501419486400d0507840100709079034000d450030000442e0208460f07419190403c030517042c440c3e591900300d007044040d44002c0d64070740c01d1071241d0f8140000440c1c0e40810080390300d074811007040c81d4034540c001001403115100040c103190040600601990401007410041402255088880240e01d40300b082041140040e160b00050411111107049070b100400c1018550514072002050000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 287767428 1250 287766178 287766181
    0x9070f08130f0b0a0204080a1406010f0305030d05190e010b0306060612010603020d09080706050f071d090402041b050307030e0705010504090507030b120706090f08061303110d08 78
    0x5002498000d200401c0c07010848100c900007810101c0194080d6403003803581d18240c0b216000100030340110341061515204091015080c883d0031082c18014410007402d480c5566220038030601e401140e1302005e02554410890301c1141d0640740e000d954802c1d14100701c400242080b00901c030a03070390100d94130081da80d1503080e020118a001d1201640010046581034030b000c902071030740c1c41c2c03103001403244200740341d40814180e60014041c0c010340034203076000041c05e079a1042882c04a0041c0001d4600f070761010755060000744814003500400c041101d205c2840728840c6494400c110780b00c41c0080c41240c001d52a014024040d000d0120101d2209035151a065107174513001c80024112010080d00080790740c082041002666001000c4805680c030320398000c80c450382d5046065004c0e0000602e80c2d42c02100d081c4808401001c0800c3d22404e50b440360344c441840355a29070076401d880c90b59010f00c1d11250004000305150301c0400240c440c80c0341c440d003040440100071680f21410064104102d2010441860 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 287768678 1250 287767428 287767457
    0x30c1d180117060a090f1506050a0e0103110411090f0307050402040b0405120309090f070507050d0302090f0306060a062d030c0e0108100e06060c0f030c010c09150804110907 76
    0x106180d03121305a0a0200907a181ca40c940b00f45a480320399010b05441c0c0648483c2c0307499081361704200041c02d406000b14580a035111604d016081c82448140c1b80e02c1403805800a01d45454003407505c0e01070b0340310506410940600e04019a82c03540d91100c99051080080004141d243c50000e80001c1c02c80101e02030321203260005010100920300c020800a1b01304108801c9a03540b0484442d400140d91040e1121540c0d0700d00061faa58422004007a00601c1200302c212403842c2d142d0018506400c080d5501000020700c20281550341005441050340103c00403002e0100ca8420f03070700700716400c002e619904840d803e0710001a602c1c48102d80ca000c0000e85503440c01132079641040b489021144280781040551510300e003841c2560310740380603030030b0b014800002164943d500c540039512031003001c1c07003610403601c00c542e0080d5407940016034201c00c80d400c0000d05580e890180050000301e445600c0c40654405808408591880c0010012242100c054544100c240c0342e655005115004646808080780c6448 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 287769784 1106 287768678 287768683
    0x18040213050a0501090b07060c2105070e06040303020303061302040512011a0f010203120703060905041202070b0324060403080f040e07030c1d180117 66
    0x1165214800100414800071a0021074100c6442c030350310401034440f81142e114100c0071039801d204000100c1c0b03041c5c1215002090518103090003090315448003040d0400503a000303500702e54500030812248d0300703d0400d60510382c0403602c40c0c1c1030602e1940d000b581c0c0c2c480100603a01a11542544015403006501a1800b40400600c5018400a0030318141c2c000c01c4020100b2107807401401c0100443e051000c10a8441c00c0b06074003840c0b41801a022460355460007a048404040e915440026001703082c0c0b00c1c04d40210310922292610f4000722100918007041078100710101001001031060901c8000c000e004801400221280b200071003100203032082c011903201809024000aa00c0060a1000000e100b602c0f80d1100f030550640314a08102c048842801203040450200f0503103100c2c86000d01125176003094001c0c00c441c8003c1d0058040300913101c00380e00100d00c1c0e01150458030000c1130705 = true := by decide +kernel

theorem cover : BRFrame.Cov 287589928 287769784 := by
  have h0 := BRFrame.cov_init 287589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 287589928 ≤ n) (h2 : n < 287769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
