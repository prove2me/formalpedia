-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0828
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:01:59.18271+00:00
-- url     : https://prove2.me/submissions/3de44f42-852b-4be5-87df-980fadf63a7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 148741007 ≤ n < 148920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 148742257 1250 148741007 148741009
    0x10227120a120306150e01030605010e06030f0405100908120603030405012010140f0f1003150e0f07030302061006050409020a1110060608060a03031707121409060703050c030a020702 80
    0x1000e007a03102d1700e100d0702402a045070050707100c400b110741c192090700c04002c4140c440004441c040c414084040d0050400c02c08280004030001728668014810022100700c1c0102e0300e070b84025030700301c5c00080722114804950b524a43d02c1c40310f40203500c844207070000d506003460900003c0080c2d0808200c424494000008103140c201c00384140c0c0840164064240101e070840140128000742c02c880b90008a40503001158040c400440c1950003000224071408c01507080d5140c00010350103486e40704464030b41e81c001c100520a010301904440104200180400c0391a508000e4100030b0018042e200030b8255910030f0007103075004016a03040c0c0d6400140103884103079040c3d003a01d102c02e0b4281494010303c64900050341d050616004102038a8495503040b54a48460003404840c0c0f1b002d001c014007040c101c0c100c2003004144521071950114035440c00d42c40108500c0068800c88000c4030944105840b050100403240f0300410406400c80b901785070400c00380c58000720040480c080601a00c82d40c07a0006003080c15 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 148743507 1250 148742257 148742261
    0xe0705070b0a1401060c060e0d0f030c03060e01030b0f0705090102030a0309050f060901020910030b0a03120c1a040b0609101401090e0c0c0d020f060406050a020705010227120a1203 79
    0x191450b46101c503491358407010080c00d581c148100c03c403030b02d0303050800720140305001007086404004142c403400b46250b1484420750190007054120820142d880d07100051480038000e10600940c020345210302c25050003d071107818490001c0c600c0e01409420032001c0c19a903400003c40702c0c1c1001c18070700010308806502d4680c2c286001c2e14108281845150240410494190300406208200307c40c2c030194444094010350a441400e09590740c860000d00f001c10102d4041015400302c2c0b030051800b41c06140e041e99030000f000d500e45102e401c840b51024204030400c611291655007284044907100c0ca00e02e0031205080e9100001d0140c07401e004201c00021546074043d03404c2c034020382000c001709002403812061403500c54000150041041c07003100c00381142c003130010851428105904015010503511a12960082c01d400343c0300e00c580a500300700e0b1202244085c80909000c0306c0c1201c840d291b8115180c0e0b603003043d0750303a00260f61040b401e42954011010000951292180d40a00c43c0442076404c010f040e80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 148744757 1250 148743507 148743521
    0x4020d0809030115080607020703080d050912040306020304111f030c180801090b0604090503040b0903070f060c1a07020d0e130518071d0402060d0f0c030f060e0705070b0a 75
    0xb03015800e005406490f041c2604045041c0c0f91000222045079907800b02c12a5502c04600c0041c0c083e030300c00c00c040001c3c0c0701550040740c2d000b2040d200f110544400b2540250250f40700ea44140c403041c1d03010041c04204104a260382e20041c508540c0b036500071585400342e06140300003002000526580b490300754082c0c0d008261003031600703c0066845511a0740e0324915806481c4034542100d132810158001605880d2600c43c0714400c0da003140065090034144024491150b0010888aa0500c209000025140c1594468001070601030780c401d69105000d180c01e110410807403c0103030444614804120a480c0d0006810311812601c1c5448002400a01c0c046071090308013980609100741072800f000700c032070601c0a60640110765070b802c071084583d41d5a04080e44660000151083d1185140428054a01000a45000c000e442000030304100d000d564402203074011843d405c00310307840312403482540a040c0300300b400904259126031033524040300000c210f1303c01c540000b021403040c5800718500c0c94095000e11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 148746007 1250 148744757 148744759
    0x5070e100c03140c030d050c0c030403030f110303040309061b0305030610030f0c0c0311070302030c01210509060907060e130e1f050609150a0302010302030c0904020d06050319080304020d0809 84
    0x75130340c1c011210106407264852050f5005c1e0505140c0419608072850040b030300d21580b008081d6041c6800d40d58121780d642d01d00100101006200040d00041003014401140900d202e505c2c9c0003211441d14070098010381441c2c0d003038028503003500b0708440403d03081012a540402c084600601011030490b0030340050202c0302c20344204a140003801000a5000300308030749100d0203902d50181c0700d440800215520401d5000094142e0082c0d0548032242d40205c4062200403400c7d44070410035001c003542c400c202c403000c569445d6207902c401c003407001c10315090007000060300551424420800750080411050405070301c3d900001c994880e030100d41c0c550f051080051091280b0b14085209112908041c0a4102580c10700c1c880c3d000030000c20115030a01440b000d003450003400940000707281d42c0055000350001003180d040d00008000c240d24950360b500c01072603201050f0314000b4081e03050005051402c810008090058480c840180c0003051856050f280d1113541200c0180360341e800c9290681131801000052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 148747257 1250 148746007 148746047
    0x3100608070318050313050d05100504061b0e0109080d05030c0c0a12020a03140a0e090a0e070806040c060e011b03180b0c161805250c050105070e100c03 67
    0x3d081048000b0000708090f290607055406000d45640c1001010844900018601d501070a1040d0b165a01604000d034068010040060220406040300c0907420b01005035000041c0000d52150440d83c00401032809010800c0040071502c69545016100e48005012110441404542034501400c20420708602d643c0c0401031960906040c41d02a640d006075040c02ca02148120444124001031642910198290342e96603014102c841814030a032403001529151016454039280440e4040400c5240f00070034030f47d03000744114039103410111440e4000b0303002007082015045c12030260381c1c0d200c1d0320b1558442c8685400460111503113015118060019001c0486095446000030510449806401c29408480584201542400c520090804680200c0b0018401124030030254402c41c2c1c880c50340070981c20032400802c0259008042c05003c50141100002c8100ea41001040800c0c007840e50000c01c1401e03c0040003000d980051400b00351245411300300b00c03000031aa401c3c1407007a83c0c1c5113a41c01e420700c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 148748507 1250 148747257 148747301
    0x2040602030d0b03010c0c03083312030412081c06060305041401090503030703020f040b03040807030f0305070206040b0901020d05010611070b030c0d0b030f010507030c030c05031006080703 83
    0x8065229004103074076401c1c941c80d20f020003403a4101800b4089540c07401e9901c070b043c1090329680c02d0b240207201500310f80202c034554240300c61282d0280a501c281c2c0c1d001412811003180710004201451146496000c0260001d000c100007000c28070241a030780f154442c1c070b902c0d242c030703006a00450203003407034880b920030b80e402c2050000d100c0d50558446400b480c05075007250540d03140c14184038240c50850ba00200a83c2c003c1000900302c80c0700b40c1c041c000a00c0b0300e030600b6161680c0c4408101c81c6801c02d45043da02a1070008c0c50030105500040504c0c0004401e040601a07440d04113406903c03050000c2001d44111b90301000500c01000a50441c2c0301400b80b41006c002c42d50711118020400800701c0c02000441c4581d0340041544c03500d02d4240c0e803141802000041c44d011485e8004e030701130900700c0b103000d40503c1550301c10045007800303001e00b520404641e6000220724564240c000c050701e0018881c10103125040080c0084060f0390950101915103070700300744600c0d40711444101d009015040811007601d200b6a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 148749757 1250 148748507 148748519
    0x60918060c020330010503010e060f070e090901020d150e010608040c081605090a0b0f040e03070f08030603010b011b110a050303070f0c0f050d1e0b0109020904050a05061003090809040204 82
    0x1340710003290a8007001034406a0f240c8061508a0743d5119513000240d129100141f1050074086000750300003501d182004c9040c10a0000c124080410b40c0e640c2c8003a50003080b01d20503c101c078810a01c08050007203c50303038040e180c40c9080e91203c4040c0121700c100400000010184044030701b03400e0003414514101c506c83d0902035001c4031107215a0103107030701c611640d0020510301c030460300a21083d00300042071030301d03e00103a4040000800403000b615480d030109200340d0b40030a140c14600c0340580d0040344113035680d240c83d504260071501c20622242c180201004000c906020408011826907800b040c2c410f01300ea40d6100140705007000380d00041d4036210019800301000340c0c2e22080e02c1000d2241c42220004c0e52102e03800e400a0300f880c014142c001d22241071a40200c1c211403045000f0541c0ba90100c8003030001ca45a940451400760081c1010700e40000e28003101c0d00389441840c0d031005040a04100c9070400100042e040040e514042041584a1940e1020700841700304994a43c04001d1045503290b0f6109 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 148751007 1250 148749757 148749817
    0xb041104030b071107060f0503090111120907150e0d0c0e070509010306080706051606061e080606030a0b0a0e0309040f090b0f010b0a050a0c060618060918060c0203 72
    0x118118006031401131404c001c2c50340051580203541d43d40c1c49000d140c941104045a40e501300401410b400d40d01c0c0c1d1204c800c20b4800d000100300308014100d417840b80303141c4100d03014684100c50f480240c1621004180114540d441800d000069130100c60010300301340c25050040b0148060f4209010788100c0509020003580c001006107a428000c0e207045c002559140441512486240b2a0702c012031000c00c540380c020590a250595010300c40c0d20001b030001c0c0c489110004418015410714100308503180b003800550410480b1070b5000c0400c07002002d204e1b250307540d4818942805400314001c5078031108420300d180f009000342d50074400050b01c208040c0003202e900101a269602c41580c5584031400070408015911f16224140c42c40350140f0351501c081c1805c200c403182d010004003800c002d25040024000b5444e03014500003010306229415007078400c40c04003003c4894552100a80b20f1800ca085c8869100080c0140d014540002c8009504e10100307030b041e4150300c0791105a425600300c190880c8601d412107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 148752257 1250 148751007 148751011
    0xe1305060c030703150803040f0e0105060d05040f0c0b0706050f1b0906160c0306050c040b18040603081209010b0a1202120102070f0c14010c030c0f1103070b040801051e0a0b041104030b 81
    0x80740c4452741603510000d40000b1407080c002e15810000030844012189040c1e000340b5003251103948140700420300c3e91204000c805032034118440703607040000c054042c0001406003e81005072a60341d10315030305020b44840b40b0b45040b11a400c1305013201090a003180c3d41c9803000c4d42c0d00d010200001c0560005607103041c60704050203010417500c0340e18103004150482e412000740d5065800e4050294540142c012100034010b402c0c0c42c1040c1e005403640c0c0d0110000d825103010f002503207030f1944004001c2c00c2132200a03095440188050780140d580401c108400e0240c2e80782c09001c16010b5507007218010701c500740c07640644924500604004040c6403560208144d100c04d503811210b06c81800b1030089070500044599482054000d000215405659004510800200751040e4170600f0110102981d000109081942c51b84c081040c0b442d0104007004424820f010361603100c440001c241203c1900c500000c401c1d40c04c064102d0000c1982e030440c0e46c403035803125030080e13021001c800d06064a540d901d180c483d8500b241 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 148753507 1250 148752257 148752269
    0x80d020a0504090f150603050a06030f11091503031b031b10050c0a2705030d0905011431081c0e01031104090c120f05010e1305060c03070315080304 65
    0x44c10b01c8801c01412144600556441240c500d9607480f440c040781240500b4020b8048441c860307407600e0000c0010281c00380181910702c00c044954404801d03408200302028010401c0340005c44031170406103a55408802c69100c5000c0044c02c003c10300c4100103052450240c0c01c01040c5400204601840940c0c0002d800030060741e444038244481d03a5a50321069450041c4182480420111030140b0060403014401c94024014001c04091081d0740d02c00013842c000385c1d140803030701181e1565414041035920000100c60f140301c83d00700074580050041c042c44044a9502810980c199220800c16000c090b04080801442c1c10401c441d43d600031103041c0356180418485820214400498019965001e8040d1980c80c0f486e05c01e10600f450316154223070000d006854440780c1040140000d01c20000c005100e00c44021100c02000581036040008511480c0030141c040b105c980070f1b0000c0140007a10024200d0352081100503180c3e200d80b00e094080d00542040b040303144044919180104030400000054811141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 148754757 1250 148753507 148753511
    0x90b090606030d14040603020a0c062a030504080315150c03191d0603070306050607080307091707060c11030604030809010b06070203030702060702120a06050a0c0822080d020a050409 80
    0x20200c441130360380381152420310384018010321080010602076405003004058604100101d42002c0c0d07107880840b03480040801e188080000340020000d06d81c1c851107400c992900b005c203c0c0d0304180d01e5005541c00000c103800170b0f43c1c64034034241072f054440310600b01d07800490380d0109448142408034951079410030b4001e12070341c1415210603030300944144101841010302c1d8410707400c0e0960f0350050201c0741d40700500407418551207810000306600ca10700117000c010b0282c08240d4036402c0000c002042b15108d98051191502c2c2041a048485008145081100c449040207520641d6915104842107800000c90b981341c0100703010001419002a24540302d014128020081c201c240405c0100d030780600000a509944188148001401c0050042003c80d0000346940254103000440c01e1a010f91500100c68081d220300502090f5480b60051410b04c0e5000c2c20a0203145c684000014520100602c021180c00200900c02060010500c00c491034004041c10a41d0785500c010300181443e441417140b0b1246034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 148756007 1250 148754757 148754773
    0x702040b0904031b0809100203040f0e220c120605090f0601060203120c07050f0d020c0607021804301e0e060307020102160f030e040c02031c090b09060603 68
    0x128004580520840d4144c030f030a0b104d14120802e45035800e2010340d04440d00305080280c6c25441d80c1e50365140600451030350080d5590350400b00e003502084000c0e03102010040c0d4990a111003110311901001c1070140d92001d8812a6060781416001000c0f0f0742d01207100034940c6504c20050000e00e4101e80d10444444045403148a01e01c0711a5035209401d2007901c0c016081402080c11542d001d61181d600100c07403d4484d0b00300103007074403841c1c10401100c0d41403100341c1c49104100b02c1c1c10b4050154588940044500c6402c29002d500450700f000114020102c009030034800160400580100750030130b504010b03040c40c1d40340c20503008101c0c1c00d400896481012481614155402546c1d40d990340a080115541d1107542e00c0b0b000741403228175000a44a1401d554086c090300e00503c0d00c211050946030300070383e40b5885a02403400c018103039007250b00e1504e01541c148024401899000801c482991510070300c010b10216800c0c8e052401440382080080c9482c04d65014449140700000d1268001c01c01101520600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 148757257 1250 148756007 148756009
    0x5040507020f030307030b030115060309140303010b19020307140105010f0b03060a050103230a0f06050f01080412030b03100b1f0c0b04080c0d1e090803121512030702040b 75
    0xc5102e03000303142c140d074004c1001402292081e00301e0321300007001500215101c0b401111100d000314060f044003000035502d000d58420310402000c0fa00040c45c072000030750700d50350404440d00314511483e10300e504c0180d00604200c8040340308104a544180d00181c41640c043c00810030940a00310030f102d1005070407a5007002103902e02050085a00a07000185054001440c010065001d020300e120a40c169490b1251208005481ca21040707120b41803094000403800c2894000908032030668025034042e51020a9604e40340e6081004541c00c207400148100380d03c800148114040c140c0d1104507034050107110300c015101e002c43c0d00234600040b811286200c60400209810310084a20910040064901031080012806a00c11990404d005403185881d050903d194130785801d12019280000030500007800051180d803101c0384544000c07e00d02809200c0c40e2042c0c4580d64051003401819007450140491040d400e100a41611407001401c3d000ca0050158070301a100c1d0480482a4040e606060a103001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 148758507 1250 148757257 148757263
    0x103061d030304051e0c0108010302040c0e03031c05070f020d031d010228080c191206060e03100e03311e0902191b0203120406021b0108060d03090308070803010504050702 75
    0x40101c6c180e4400f20039a280d0b4081101030032204070750205201401240d010140c0382400181085224183c0e00045d0618503a5a18110307071008180f4020040d401342e054100540c04901403010b030703a03203103804103025002c5501c0301000d030349605041c8520f40c03000400c2c101141d0750440090707600c1c00714603009001180d110760035281d101c801c8581690000c81048071560300d8880080445411a01d8502600c1d0035024400d00b404840ba01e4200303c2c00f0806140b082c181514081001141e00740209106101013000d80e036095035240030303010349541c01300c41560b1301201d80190402045d9a21500c0007840d40c24079565400c038428000004d458203400250301c9808540140e0600031501c4070420a80340e80481c06c5582c0c2c080b924007010010b46108583c0c019400310160f90f08101342c410850618020940c0c407450a0006881c2200c2901e000788001c44a039400907075aa0000003281e4407030002c0c5c032100c420710720900e41114080d4413034100504c03010b00858101d040c002c0044c091816100141d40400c16511285401c0c1e039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 148759757 1250 148758507 148758523
    0x30105070c080d14010e060f010c030207091109100806090a0b0108010302010c080c0a05030301060e030f070e041a01080a0201032418061a0a02061b030103061d030304051e 75
    0x8003141c009006140081e07480d000519185180800006003000c00801070071301c40070300381d000307040c1d030780e0030205200a41c03505a500d038407200424201040c03001c29503031b000303074641546d07100d02411305a0361686c149035465103901310307104d094005002c07181524111b07002600b503110980300d4901400d4501c000442000c03581c8074145003003005031a500307542c0e81307075900454580d24500700848881100344141c000f080020845010858407801c00346440f1345c10060014001820741803c00d00c20f80c041c200314203180d0310114808082e6407840110941d076541b40c0c100040308400911804003c00010400080c0a0030b0201d04024180c5c801d03603090108400409051002c5101a0981490702230700d41000c00043c0b08090314565155170005c2c000c107540e560b8004446109083da580710b0005100012a54804c982c10700031564800b90080c0d5800c182140c1486000160005010041406035143d61000082c414002264008022141120341d01d191500d8100e403104032400d1222000340c0d420030360008954020403061 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 148761007 1250 148759757 148759771
    0x20c0d03140901091715060a030c0b210112030f0302070308070c050c040e03130504060b0301031401092103050c030118110c060117070501020a0201050f0309070e010609080c030105 79
    0x8001041c0040c0c280341590240740d00505003c0320f88800141000000c01a10352a043e920182110840c6080c68000001d0024480351155295140900c00190666003031030a0710000b20102d51210402e014002100c400110b42c13000e410044000040c0415000034002c0109100380d60300ba5400c00c003c1e02c143c01380c3c02100c0009002c1139801c0c0014200500c070700170070b000d0725014800301e410503485900890700f1034808410039030054100003005a6404124800b0100601d002d5808000c03852808400d10700f0b13808180001040d000140b0030300011280f094000e2066960000010b21340b50100c90400404c4542c041c428001290a29000550309074568003520304888294080c06c104411902c1440000c00180040c07202c020310a001400d0010b5080043c58081c052402082e80788000b01c0131803510f0310340c01c2c3d40164111b43c006601900140d0748031068446003607085034030b2a1262542d0440505004c3c154102416800000000180c1680e01c0702120003199400130036100c541e0544400e050a03241e00f29039034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 148762257 1250 148761007 148761017
    0x150307020d171815010609140307030c060503190c0806041b0816120509010e0f0f03040b03060f1003051812040506130b030a06170307030806040c0e040509060403020c0d03 75
    0xc40d100780d40038010f41003003240000c2d600c40303c03c000c85400000c80203800c000c00092806031309008940a00700000c40c5030354100c0040900600d16992100100b1050007444108100840030408803110006904039501592030b0510407141c00320b10060100c40112509881507080c84403440e402445600355004110440e581d03040c6d20781e01c02e450039005890401c02c01003000140d41c0c0c40f10090541e803045a000b03454410010680080c0c04004034a06400c0c580d25004940004c0b810f8a08001c002003160120344819000704c0e1a80d0f92640041c41c0c2c3d040c0c81c2809034124070840308103400070f9490340c091441400d02c20740030001e59015141c5269501041e442030403901d0300800040c441c603d4050094009400c0c070030b131001c0405485880d800b40d00d420658100480e1750b101c160030320964a90b0b26030740c0c002681e560002c0d420301e401d0b61401051854090601e40c00b4990324613044451a1054404440c0240041c0080c005800c0c400340082ea520f030100d03400d500502400242c02e1141c0740c02041c1942d06600340d0b030340d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 148763507 1250 148762257 148762261
    0x415080618240105091c141b040c03270b0114030a060506030a020a0b070201090b09010516060e0d08060f0109121b0f12110301020a0c170702150307020d17 68
    0x4504510401c080707402d41442400d1050b2100742da541009000c000340f6120101001c0314281c40d04a2540103402c40c01402c0d0340000342008824480d01110031403281c01203e0114020030104401c0c2c2c010301c0d191170348110841003070310f14000c08a40c80740100a001c1c400c281d500b9070f81c0e903a0b8607030303d942c0462410015410b41204904401060040e04400e030458801020703150030040503030020310042070b203500041640d03401040f050255a0002080070060249000c0300d890320480c8000204140302e080741200482401c0d45c48442401241d9004500011000d411502010300c11607025041c100c00715640c1e0f100c2c00c0304a99241c45c5500c513414650444403003903c2e104050300c660ba100900d0900c122000c00703844c041c030440002c088e1200d1181c0030041000e1b9001058001103410480d41c84001c0c441c074170740240c1c0100245800243d10020200c5190340214a8410355000c00c0c2d032244a41c440c260300a50f00007004140115018a402c0c01503018612b40e03002c80741120b110f91000d035546c81c1d280030074280400304140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 148764757 1250 148763507 148763551
    0x3120c081b0a020d030f18150b060414010c0f05030c07050a0b0c0c060705030c19060f09020603011505040506030a02090907020120090105091f030e1204031202030415080618 76
    0x4010510081003020540c0c0130300c01da00c80d06841c50604103440310011200124286223451044580f41c00080e10f1030380c5840d0500300780890300d4010224060400100c2c00c0001c040c440c1c1440c4100c501030b0b012003a00c0e910280000c009070344103070754056035100c1c1281600c0011540f441e00103d82d0324000141c05050300d81518030810080b500002c0042d03c207804200301c8800e50050500031301d081102d100314200444030f03203420200300b01d9140060801e01a403600801001680c0c5150549044075000c0144c42051950100100c4890066030b1000b5008071000c0b05019010f50b07281c02070010043d09581e00101a0b64402c000c9080e5801c80004681b407c01809080104003200c6005151140c0181045403504400c03002042c1402c1c050b500f480310742c500b410f803000e1989a041c01074800903400c16006000040038865012494800c0d40300c01005c5240344104c0150041c000d0094030010309444d0600800100503507409030109500700c80452145520304801c189180d01001010b00505070203d00c02360100502c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 148766007 1250 148764757 148764761
    0xb1e03060315041412120c1c18060b040c080a0e151003050d020d1409040902061210090603030e1002070f090c140406020c130b0418020405090c061603120c081b0a020d03 74
    0x41180d480d140c059083d2312034000d002d80a8403014000c500c8203588844640c0c00c00b05c1c2200c002c411898400c13410010f9041c9440e901c41002c0d500701c2aa14000100c11500780c011a107001540015424183c42490030041e078403c0c42038404049034052001e0b110480750882040784c40e132400604050100e44040b0204880300e609501820001d14081d10028500c0901e80000d0b044d500f010a59142c00c04905041084100c40b000707011008011680050009508655000d8080849100a03c3c00382e030b45042c80c00c082510170482400104488080080300c2034031038810b800901558150b100214185907080c441380c62480c030490f02214420760280940c0303400d9030100013114105858170011240c40e0f05c01020503507038030720414400c541031041c40e000801391481440160313603000741440c14640040d040d0004a40315042200d1a8204014010084507040c0c98196031070010708960020b081e00e01003440d001c140d003100599000e0f000ca65020001d90031681c0f074044051094018440c01a001101c2d0104154066 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 148767257 1250 148766007 148766017
    0x2150601020304170615060f04030b06060403080a0c060b0114040b030702010e060c0405010207050a03020d0b040515131e0309090b01020102041502030909010b1e03060315041412120c 80
    0x52068a00e0699913504169040c400f9200c15252a048103082c04420020070802c4d46c00e00d50182c2d491410074005010161080c01039100240040401a0000c0c00750b640340c5088070082c3d41c0c0103030319540b81c0480b900c0051200031400c0040f0ba00e1391500600714070a40c00780350500078800110051500d40381c10210910465000a844901599240c49100194040c01e001c22449014140b40c8a038689103031400092500210703034481402001810810b0000d41c0301d803a00c101c0e1058021440c1b50309512285003440c50f08941032004010b076803404003440141c20f104003646513010300400450356104480d800514802000010081c00b24500c0a01002008070381c6d0003600034070105000041c00d00356a4020085551004010080140c200144800352071512040f21b6002d001e040b0006130400c2d01640346070a06269416a01c0300450002c000264903035001c100c42950010403080f00c1030907040c545090800d450061a0f005d0303060240c51088011681c0c1c00f0140d86842500c241001d0f55501d0b00200b0001c1940310b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 148768507 1250 148767257 148767259
    0x1e04021c05010501180c0503090c01031808040b09040c05090f0f010224040606080a2609060d05070206010801020f040e06010c08030705030603070f0302031b010e030115032001021506 80
    0x6040da003201040d420311031280200b05d03680d00505030405240031541110316012405060000a000388040c0c0c1400050044c108502801d00144c614402810048081203003a4000c0003180009000b01d017001c030080c0a001c004034261814041040d14a1082c0c8203400380c00950ba8000d04040345a521502e411080301c91000c0041c01074440c07440b43ea45c40454103180d000c29602d03841e9654000e03c01007015500c2800014440700000d0702e00400c0568030202299482d01c0c4405042e940011170060000e41d030780441c0c2c034031400100055a01c4900100d02c07005030038121110300250040c40c00000b65042c06000301c4040c0da17034080513540792604020700400601c002410305810840076005032000035541030002c0d40100c085440e803646a2a2900c1094641007007030300a0f40042180b045e04100507200000e20540010740c81114100818100740100c8041e0440e040c05641507081ca048140071229040344401506d02400c0c5ca6028043c0140740414929205c1c0d00d0a801680920403d8948006d8100e0483e08010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 148769757 1250 148768507 148768549
    0xf09050303131b0e090c0f0a0603020711040f0c02100b010c0602030c0f03040f12091505030a0905070b070b0a0b0a060f030b091608130c0b09361e0402 66
    0x3c3c1e10341501c0c0390f034200310301e01d41da42014042c81400402500380708010480752502c1c920000000b2551604043c8a0b182c14150045903d104202d000242400512030180c420000700003450790410182150392507840150003111078002ca0b4011901500c008400e041c3c40c0c41d44420305654070b090082d40700070015801120240302403920065100015030050340136800740b8940310818141010300c050071401160601c00c22200c01c000014414107071100d03800c0507041068483d51800002c0b000b030812030358000c01600891001082031070f2840082d040050103026490321a50b07515400004940c2c0000c2030f66886007a074a4104442842040c81d102c0d420044d260224102c490400800d686040075500b14440700e0b03500c00c1c10781e9405d602031585a0302a5001501a42c4030005840c0c941b8074041ea801450a034000024071841991114400340446e4020790031840c0c01d800b4209241c1d9410394940c06105080c031031044c0451100364005010070b29003122402a0902134440790308110b5600e00c12104400c0f561 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 148771007 1250 148769757 148769783
    0x3180a08060a0b1002010209090403031a12010507030c030513020d03020a0807080406080a0203060f10050405060c01021305010207080615120303040308060102160608180304030507080d030f0905030313 88
    0x194050101c070740540e28011011854052000c100413208a903a52a4400c6a00c10b0044010981d02d08614a4115030075060026601e040c041c03508071501c4107507503d160442c5140d02d83c40c0440d034055001511803055940c04100c001580101182070718820340381e5841040464200802518048a402c80780c10310074012188080c0c00d17a9541101a00140000c0d940364001150070481d1641001d00e480d405a90000110b180d450400c00058402c1d07016a0703441e010300d0b082c408100c0343c0ca0040049030040c00000f0078561b01c8140e83d4158601030742c0255100314060505240016055000207440e00c190342511001e0001c3d42e403190101044903918292113507200c40d0f20020200b00030800d00c01075003e41d001e035950b805c091800d900068542050300c017a6100540140b54100043d40c0e000810b25088114000070742d0400074050022807440c001c94201401c54004d00c01d00081800700003481070682c1c14291024007029452911404c122041072102801d1500100005027510039400d1280c6515031060030036141c0341c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 148772257 1250 148771007 148771019
    0xa090c0519120f03080a02030124051c05090705030d02060c0d0204090903020a0204050705160b040f0204051f0e07050405040b0d08160b0903040303020d0813020d03080103060e060903180a 82
    0x103002c5481a1a107100040d451030525034040810b5a100710303a4103066245514102030b4039144060100110030241d081c070200c4610701d1044003104d90400368426055842c42e400f005910082009865159151080d03c40001c0c481c1400710355210112495006000710740c0e40e0894101103503001c0f4913102951a8200004607074525540701c1e01d49428004c1d0f000388850550b03403041c04111400601694240b10051000e107003040400c40303000c200d9942c0440c0700102503d82c0d03d01020b01807030040009501508010800c5004140c1110006003002d807010a040181c0e42d501e01c2d506103003401e0b40c1c03d00008908010600107801e040d0408442c440c0050546c01d052062178503541c007035400c601e078040284003040500406122540c1000e42d008211100034514051540c0c3c1c0195907100da01c004441400542c4c400118230f034000e0050299507036005030101501e051a4034005218ac1000d01048625038580308059214210015840d4170420080c001145413110f03035a41104540d0740d400729140d0004010f0000300e10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 148773507 1250 148772257 148772279
    0x1206030807080307021920010e041406090a0b030d0e18150f030c060a080705120703021b0604030f0503091006080a0501060b0703050306090c0706051504050a090c0519 73
    0x44075024103800e94032400c26000c020705040d10f030340d425104519070303680450100300000e05903058800502c082900e074010103801a47e03042107070340f503080e031081c640301142100700c00a40070b1512076141243d6001c0c5070766038264444110b80001901355050b0744000b078032651940c01400311400354803004000031000c08000030022555030003103a048080d16907078a41ca06003401c1440c45030b099801d0032000751160802c40000304280d03000b140802d000b003003002d02c04115958095411980ca14420324411611890310000241c003a50015143d80c00d40140f0a60310480c00401041d130900803a81943e4454021030500000c80340c60304060b0246c800c0d405003500c07100d580c50f064403c0d0002450002c000c0c007811045810440e08460603540700007100d090811228001030340c00411207500003422602c41c8996111020140351602422100401440c601410700c0310741e606007001c2a5031000c04942c103004603030b180c4400340e01f0ba5001c8000200300c20080f901c280042d02e0306001c40705086028044072070085a5600790b000c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 148774757 1250 148773507 148773517
    0x20d0c09020c0a0204060501050408060a020d0905030c030403050c0a18090201030b060a090512062502070e010311090109021c0b2403071701050d060c030b0405010b04140409030f12060308 82
    0x4140d11452070102113080a0046c440100401d00348581000d1030902400d848090007007400da0341c03e60000c0c680c5d141d181d099008001894100003100d49540070b010003207039607038480e0009035000d00c0759004160b410b1034016001c0c01680c0c84807030400d22811038901008007901403544102e06158a0305071107000c60b03c510703000e041c410b4110303914890180c1c030301014049842ca41e0301e04c00384103420420030045d49001d841200c0441e40c48400112904060103c422800c00031983c000400681001c3c0c000424040a007040ca0008441261215110790303864a00c04124800c84110480e408131901241c0c00b01c0c034840c0e00c00c81d400d02019000205d0a09205c05031303e078804011580180c003120100600c084164084414003061002d07148a0480e9414000080c500c4070403154018030090b12114018144c5119802150841c0405002888596152015519107030014003030000c003031f051368140e0302007880c0c40d00132070b080345402d03031100d5101c0c2c18140401c8809041c0f00e54034500306600e44200000040d24000144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 148776007 1250 148774757 148774777
    0x90a17030405011205040803160207030f120e04060f14040f060e16030209031c032319050f040209040507030c090507080115020606041a1302071b060507020d0c0902 72
    0x255481e801d28001501800a0034598440c00345403c0411000a00e00c0342101d1f00700242d8007400540c0750030503200b00d01d000c1c01a00010700c030601400082d000c0009440e01900c030844143c582c0040c01e4100805c1c00200d03422071103510031100c842c03078041104e094030b50b15900d0059400340c0046413245d10a805107090f22900e07801030020710199010001d0341c0036110010b40441d40d90b03203411361400303001d180041d9440703182c003002044444043d004000e00354069402010500074010030042c00150340c0c051100c10b45012111104192a0340710101e14402140c0328092151000702c89207901500d4070740900041e9240100101e4044c03040782c0b0f01101040904044038010b2400b01000301e01880e080d10b00810005040c1d0100c8400502d28604100054010030826401a410b48000840c005407092401c200110906199042100f01c42c1181e0900c9641e0010401140a60814241001e04116482d4000014850398000400c10700100c0b0040c5080d458039143c45001d8941ca5402c542c035650384c10101e0780484510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 148777257 1250 148776007 148776013
    0x3030216020d050d0207120c061d10031505010c0c1205070f0306091110020c120c0d050705040518030a14130b120603060105030309090901061a041d041205090a17 71
    0x84203031307a410403145015015640c503041254000ba80d405204003228000c13030080c403000c820403416142c0550200400100010040030361459000c034094001c0a840b0300710030f420740703003d0000310fa194003c88101825603480f8061500172854800390805e240340e80d0404031f8250165800004064011298082c0614094400020002081d1810300200348900316154011002d51700301c03194298010900d481d2000050701e00c108080c10f8008902d0515502c4012240c0c09000301c510142404400035801064820580301000341d5114449801d044a000710300d080b61b154010421581018800d0300b2108426011440d002e00f070100c452544450100d245e00f0192259201040e00c0040d06000b21a4640001c001d401420702075040901103516031140005450007600b0b4000410503101d800d600420080c01550140300d00c29075100c9001a203a801072145180c2c041d01002400150440300d9103441c092a400303c049400310f2010103080d41c10350084a81c0c0c0b9840b1040d40b900155210240074180d2041d1041300103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 148778507 1250 148777257 148777273
    0x20a14030c120d15061d011e030e0f0a0c030215040e0a1e0605060a0c0206090a0801050403080f0907030201031a0a090e10090213020f0f07030801050103050708040b010303030216020d05 81
    0x61003c0340c251a04424402500c04810085c803504040c0c4039011074107494112460b0f03d0740310016600940142d60b03203240041d501140c110030513410347c00107049010b00340642e000c0400d000c00140da115401500500100d207401d2081005180101c42078005210803c1c03541d040680d142008101503404642d10400b503516000703200b03400c2c134003240e120403034051058042003114240f40114503180500d03074046090060750300e03004095650f0312091320150400104080c00103610b90145601030401175070110081043e45022030042100c10090611a002e440003d0041c6840c640046001e80740404001e004a4000321021030142c4940718071202038030403424082180c1c104210380600e1b15140c8078000d04c04e075151803411001a0380303006001c10445005140940c85000d0414100524440c01c174081c1c2181c2e070002001030030076400010740c40c1214001d0b00d0030415603032083c000f918060707030841e40100817040e55401400003d00941c06440101e140b80c900000140e03103580882e0038940300c1c030350035141c591141030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 148779757 1250 148778507 148778527
    0x3061406010f020c01110c060c0717030309121c0c0e010f0203090121020f0a090312080105100c0c0803040308070615180509010b040f050403030506040c020a14030c12 73
    0x1101680184080c42c050802d000749540003500c03807400408040c104900c00103000c4d443e140c03c0040211a140052009a850810580072551900c1078414112038490b001c40c41c00c83c0c2070f00071096a01c500001c4003c0c020700000c00890ba01590300929140c2d02002d0405503000401760f1501c40c0da90201c10340d0b00ca00c840c2d408140009005503200406580071507100f04452901ca980c02a0b0819141c0c02204840341394a6186401d034010340582600150340702008505410356641c018902000c2780d00031204007211248580302150520000d02400c1d80040001500318000380c810900310b2030843c0269281400b041d2200243c6007594402e51083d1460080403ea05090156030321445030452411920140c0c6c007494100b4009140444800e03905955a44d400040e4440a0a401808485400038420001342c0d07e45510100100415202540001e207800001101750510381714105405d1066002442e07000ca055440001d40942c4004281c1103010a0001d04e940260800030641180d446a40054446100340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 148781007 1250 148779757 148779791
    0x203090108090303060f0906130e071805070504061101090804090b0301051303022a130204090e0c06040b0c011b0801051002070e0a02030a02130905060307143303010306 74
    0x7800c2c0e4040c40d0000c0091102c42c0e5201b030401245048140c0c1c4049070b0756100e0000a03ea034000806e080b01c414203003a00b0702c80241c004283c2c0402d40b00382c40010030b540311100d900142222000ca230b042d03020072420842070000901074140c1514810610001251445160352140d5080e00a5406040c241c2e032140b07140c640c1c0386800c3c011a82c0c040c0445031000c124a449440095035000540d94200b90a441c408a1044441c048490704080401c040d00f10031740310300b50043c1000294030920900310358a1500440a441c001d000c107150104010007030800d402c0604152030108558405030400c01c5035036036038400e0001480e00e100c0750b8000c9034150b2a03c1e54590314107014080b0780004a040001150441c940c24410300d0400c89020360040c440140040e16035840003500c2c8000d10900b544181482c020540008003180c030398000d6449041c09030147d5000e1a56684c03041d0078440e0101d1030340da020441100b4020320918280d15100e00e802200f040c1142c5600d9002c1c0d0103407540c42a08181e4265407030300b1160340b482d0942 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 148782257 1250 148781007 148781011
    0x2106070306080c150c03120c0316080f18070e0a02040e090a0b04030513050d0f0606060e0310111201031407120b0610020309030709060504050c040605040b280203090108 74
    0xa00d01802801040d440011609034904c006254000d4011454101180040082e2071350961010303001012410104a441d0300c9402c100c0324249443d049420745034003103120b4864240155000e502c40c008030b0b281e205003001e000d02ea10a09452a01c03c03240000f81a81c40b45200501440b42c482c0010b90703ea060125802c0b05100090041841341d101d900000002042e0a40e5154880e80515015455214211100c070b40c4100350380c0066440542c4c00d030f031007060100764502c1070324680c030814007007280507990801610002d5450700b9055041c1c00820224500c0740c195000032040c6060040340c41e180c128980c1070b03401442c0c020303042900d10b6541005920020001042114060101040141d01020300c2d03650302156000028040ca002d0100c854116280600030415605018802819112905e4613440710304000d09040c0308541c4102d0030300000c0b40700118008210b909542540d901c00d4505420040b41000daa0b01200300c02d14055048004c0400c51040e0050b81000c020312540619a116882d000043c400400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 148783507 1250 148782257 148782269
    0x42a0b1c0504030903030305100504020408060f100602070e04051221011a0405060705010603060516030605060408151b07030f23030a090524040c0f03030206152106070306 75
    0x1d098180300c08203400c420240300303d03a07140c503010036a540c1e0075240760078041d0664403250b00a400404d0102d00c0d00d50109071140700b101d11a2225819a44c1c44400001300007040c030030000503802c004010320214811058035540a03000743c08440342880e0f02c41125000b0782c014a5044084031021141c0e80625522084040c01011070001c120441144808050218413407417143c1480340300c0000f04441000429081702c4011600094100f1442c41c02d0720142c4805d008104040300060b00d04071000c5040e00e0140241d0301919140001017003250320b00480c000c50341101070301507051030f4920b040611f4080c12003401000c450f403084c0d50380c41c2207061581011340900030386180d103400c00d0000d0313550070b54006400b002d40368400920900803500c50b800b8100b05003000c03c0d900d52405d00121904206444207005010a401984100d080007405641d40150b03403084460382c080100140c0203080410104c6001075141501010003c00e0b4002652000d0700c510000e11600c1d1031f5002c5c0d07400400c00c2110310754242c401c0b80c004000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 148784757 1250 148783507 148783511
    0xa0f020a020a06181406090d1b1806050607050c010f0c0f060c17072a0804090c170c030a1e1e05070e030a0b041b140f011106042a0b1c 59
    0x740d42e8000840c1b0740070f452a458080d0b5502404442401074031540030b011213041c5541e00000d02c0d100c5201c2c12140d02d41400103100c00e41441d00028450901c1001c03aa0791541010143c019614420011101c600344c10303c03180e0401c5043c9183e078000c503064441d00300c840d034441c2d08006141a40450040e1283c00425000007550b01114100a20703160018070300e031186500d1041c0d401c1044402250b0710640c0041e4403001c0e015103404200411000c103990b1000200b040c0d540c5408a03c1c1c9007404441484c00380851b50a229006c042c00800c490361001e03002001070f1003100319901c3d54604201c0510703003101c1c04030141d81c41400f100c0310b500c2e00b083d0041c03080380e40001c59403400c1d00f80f901e80c036004699030700050b180042015940c8800902800080c018107580351403d00f40a045a59607501300c480e0402201c041e142c030444103402046101d602403144402882090405407031140e40f941c40d1a0b042c001403120341d0000c4e0b007071810245891851698080050300400d600c10707072117040c1c2078001d42d0b07140490032601c40003074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 148786007 1250 148784757 148784789
    0x30f071a090307060905030c030f0904110403020a031203020d020c01091a070507110a05040c0801030b0709051c03031103090706121112040602120703141b0a0f020a020a0618 76
    0x40101c111183e2a030451008540f4415915045140d8401c0300590081c50001142608540e03519030020800814216414016421565405203076403140d448001e60190801c42c04100050600c03040b03004800322800c005082c4084000c00300281e074003034410000d041e50745003202800c01500e041e098054040d064503007425407804a0300500a44203091007d062010b551030030701002c4da0740d20a00700c080c200281050000c003c0400025000940a010407110880703483c00050051303114215000440d40000d1004484c10515980e40d5011880d8007815400c06807215500800505c0b008011030040107094018001c16180900062144110301a410040ba04142488500c0c5440b8000d5030b07031a10445040c085c03203407990f16080d0020320802d45c110202c000c82101301701000c0d805500c02980c004d10400c40c02d9450303a407854903841a10060380400312808042c840c0d501c01178881c002500503203204d40120703000101c1a03000520940340640c05580002c1d20131110044580d00b84004a009100800c4001c0c0c00c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 148787257 1250 148786007 148786021
    0x120b1305010312090302150904060f090912020d020a060b0319050f0d050c070e061212030f0109090308010b03180a080915032a1c0501140a0303140f0c030f071a 70
    0x504900400d8500d01f011802000a131350720fa10010080009110a400684e030310302501028200103001a10140b0801441000140c004142540c40021550292000c026039130b0302c040041c040805241d8041c42848106d65043d08001c0c4e01c101c1c081c0c003580081104141d0351500c60710304086c2d400c0d003004201c414000c43c500c03403c0c0084d280702901c0f407110310031242da624040424a00c40d600c420703412242c4141e0320f81007040c969400c0114055030f0501d141100c02ea8aa030304820540b81020300090004000100400281c01660b000d150001c2e44954038000b01c00349284040d1400344100f0040e14034410018180000303203850280000c0c8612201c95403815807030406c480d00340f01c81180d60160034840c01950f41c3c2e8100c458001c200d6817840703040c103040c3c122940c0341d604041c01030209010f000044400460b14002500d0003a0f0340e041201d90595480ca14441000c2180c5003e0300041402e50301240107003c5403502e482c051019003a9201c0811389243c9540350360500070102c0800748403040040c01154280016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 148788507 1250 148787257 148787269
    0x3050a060b0a0c050f190b060303070b0a0501060e0105040501120c02160b03061c1a13080406020607020f011e0e031318110f040e0403090e0106020705040f02040b070201120b1305010312090302 84
    0x1b2150803032944c0303103280e80e9400400e0031403041043c002d10704070703000c01000019401c9600682c10390780302ea9549001101102c0041d19a4030075801002c0c00310380601078125204502d80c06c15001c00c0c1c11441541e120107689120812460003a4214142d0714202100300401402c1644942c1ea036611503a14002120324907440e4045918080042c400d034041c01d100c001603400c1c04066a182200b6440003009646503a2000025162403003a64200018010351190000b0a5014011110140701d04030080c010007030100c2250340108480040d41000d030006225110880000e4030b0040000c0130750b0319000825100703030100641122019000f10340c524505201042002000e0415907090751a902c840427210b4407581810307a45004150700c130341a85030b550340c004a4011344c04102e020458400b030720700703018540300c07141054140e0256004051094405010350800745d0720030005444901126070000401044410220381c041212019551000b62100c00400c100702410168110840040c5410007159045500040f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 148789757 1250 148788507 148788553
    0x1902010e01050a030216120813120318060213060807110601150c06110c0f030711010c08040e130317150f04060b030103110f0108010e010603050a060b0a0c050f 70
    0x810418003040000700c2d80d0207641110b011000700d0007000d1b00074034140b924181c403101800e481e40c002840030303000c40c4000c507844904000d83c5500142d4040b107504070480441c02071140344811515a84a5950304011500d01e1008220364105483c10726000790420030302416019018011504000461482c803003403000100e00c9a0540d00c0c00116010700400c884404c03a0300311911000600001c0c13400c0f03088a44c2880660082942c1e00540c400e40b03c0b10f4110a04240e10f80c0125035014090a81d02003072440558401c490060002c1c1c8604001403c0585518090aa03601c0c100e4070900d60141040c1010300f8541c1200616940c030b41c00c100084520714015043d10f820420040c0d9860144152422248450307407903401090151680e90b000607100d696904005c18506682d8500c00d004480d2980024919441280c03100c1c1a20740c00c888801c03269181c84022001464001d003802030080e40c48038003107491384000009040602a41d61045040789440c1447c5c1e041940c0c011940c6000e511001e1400140100501012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 148791007 1250 148789757 148789759
    0x308030a180206121f081b0d08070501050106170108030a0c0203070b071a0109061215021308030c0f3405030703080c010b03010603031202030601110d020f1902010e 72
    0x1040c1881c0c60240500c1920207100020f40c40480030400d20020084040c103d44140082070310507903a18000001001801d03018003407a05580c101c10694000c482e50484e01c00c06484000e02022845074041d04c800300103402c142c1c4201d88594540004000095102100380303c141e98014501d41c82e9407400c00081c0d0f403845030440d2034080c04410102c140541d038081c0020002001c0e0f500146540b09070518016a1520343c001c1a039007950000340011035846414031514058610088500903102219291115142e0000f800d51f851103808008038903503410707440000301c020024240110303280c59288100c5800d0294103581000380d41c2c0140042180c0e00242c2303807402800203450500c80341c3c490400903050300042d0650001c1e41c0510548100104211083c00101308807070f8008000c01504031401704141c2038034551322014000417440c2f00341c6d03100b400310307540103680100c414107280800c0340340c985081d400c0031052014034000da0082c042030828020148040c1e44031542651088401600560001c1d20314440d24841e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 148792257 1250 148791007 148791011
    0xb010512180d02010f050c0702091f03050d08150d1214250c0b0309071a0d0504030e040e0106120b0c0d0207121403100b030705090910060f0206010308030a 68
    0x220310054030301d201d00e4403204940410b484403201e802c0c1020340a0001c54142140031031504c400a0401c07a40c040a89006036030040c44208161600c0f000e8440304030301e107465000c0c115000c0f440000003440c100172800c3d040401d07850f00101441c00615020508120040e00c0e8081d074a446010000501540c00940001780c080c248118080c14503018896140503940c0c80b0001c611844000003081446084810141841054002e110b952620b8800005000c107070748015859004800501508286c0904c90515400b1404420700748040307075a0f120140d030002d40b0700344c000c1103201c154070fa406d04207030080a040c1d2001200901c40c061030059a107200002414016050703540510200b10b000c401102103170341441c4110820342d1101c15a080c2210210300401d406004030710303207409a001c8104100c0650348600e0400d119884072a140c05c1044d05a40e100618017401c016040000341c0c2159a4403180b01d001d0300d04954440501d908041b806005440d04c80010825584241c0040002507040021a0b41c081211100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 148793507 1250 148792257 148792261
    0xf0f09150c0c08130329190b03161703181c20090a050c070f02040b041107150e031c090b0703020705060703021911030d060b0409050108010b010512 65
    0xc102e4200c41c04400041c0311050010b2640c034901e0442d030410040d20300035103404148020180b0313076804445c6d0304590320809010120000d401e45881049000d0030903001d41c0c01040d141907003800241001b0304288c0300480c01020f05070510560340610f840d80fa00c40c0080008500d08902075420f03030301d109100c0140f140300c1c402100d00a080001e450804500d06a800800c001040741c0210340c014007070400100c95401110a40005022070080b409080e0181c2003130b07424145422600d0711213180c0702500002c03d170707041074441200346c6803a25284a45500f1082000d1640e440b20203901d465014900703100049860242054546018410040101c900120030f04041040c241500840303c0050246d05101404051f00e09042062240c0c164004051151160b01907400c1c9903200e84054049000391100d92443c0400041c031604280d00841903a0000403a5100b1a41094801c0245106071441a0408250007001160400541e0078a0080601605809001b8403401c0003182c00281903000303c8102d41d00941030040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 148794757 1250 148793507 148793531
    0x605011407061e0e030c06221401090b01080f01060504090302150a06080a0b060f01080708070f12020a09030c0e010501050d050c0909090d1d030a03110f030703030f0f0915 75
    0x9000f21240300b03000144040d109441126899421a000c04003450081500054100d04c08140200c1c501c04050b41003801101191640326910a038104900d00a658840b26100480c40182c83c446c002c141e000010326042160b21030903030a48038184d01090140b41003914140029401003030360314941c016a1010b4440da960041800d0182c852588240ba682c040c41d0350719018405808060b034441c4805598000510040d0401100c07038001c00c44100002607220700110340081d100700c9078a0b62203121464910103000602c00c81c04201e0380801c01c000041001c60710b0800030400308001c0c0d40d004149045048403079600d44000602544101e21540030020b548100180c0180c06941c240d0b0007150000d0104c502c20311308200650340d1100726100080204140e244400490b4002c4c1201c00c40200703000d006802003040650302034034403070500c0540b03524602845500c50441c40080000c0c0810354080c1e035002c10362040c003031300700c40440e00031041c1f8401407818402007034041902e4641c0389011029413840007400e001111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 148796007 1250 148794757 148794791
    0x117090c012106060306030b010e060915180f01030b0115020304031e060f060f050609060909090c030f0123071b17120f0c0a120c020a06020708030901060501140706 72
    0x2d0307480b014a01d084008110180d050f40868240c81c40b0346500b0440e80d8a640041580315802c44405511116030f00001c0e81c00380c045c41804034102d0025000088124035010704ea210a2001c60b1804000d03550100104240142421003c5c01014009241000190b0b0400001d4807481180405440400b40c111504080c0e05040c0200d480c1d41d80002007004400c2c0f0404419016101d00c1c170402450101c0901c0120341d503e032010803071f41840307801026186030002c3c0c4010b000d648000100803d01038003c2c12481001030b20140005060040278100020381c42c68005096903003030088180710b40c610b0389007204000700b4030b4100c0d0281c1c40c4135800d800d01036001659072811201491042c60010400c09d80810280394002d403160303440380600d070244152409035807451500716480c00307540c4a200004501c0103010719004810b62100390459030620584060010340c0d101c0b40d0584e403003103030110741d20140041049681c100071f1052501800003441c1c41c02c201e550410548000b4014060003421107a80c0700142e030b883c988a8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 148797257 1250 148796007 148796057
    0x702180907031707060b03072115050c0a0908070513022a030a170601051b070305060c12060d0b011802130e0115090b1207032301050117090c01 63
    0x20f100c0d410030841d4200760807519004448221451400e01284e4600340c87c0200d026816240a0003c594419601001c1b84904402c001c0080c1ca149821100424441d1482e00517107104010718010079540d0b2551402c0108800000c1d40620210b4000c41f07001d204694400071800018102008056211a0211142c0110071481020440042140d547e0410300e240003102a009440b1151a41400c00d810780ea4000c00080c0201c5141d400603100b004903610500e04010390803640030740c0760119014070751079546403441c00c20151000c42c260600407903900409100350141c20752001c0240c441681c007103d540d40f8882040018003e450490440160200421381d2a0703065681c10b49a20341010140d07942e542040d0850402802400e4807018003e503c501d800b40101c09030411903d503242c280b4946160400c580454580181c418003c06440c0c0f2115072031810440c144d01c00030003030103c0180d2203500d00700016022910185031011000742c5581080780c0ea05001c109800350f82c10a0070314114551070009212041518 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 148798507 1250 148797257 148797263
    0x90609011b050f0106060504080c1504090603201002151f030c090501060c200607080706060f1706060d0c05060304050105101208031504060b07150c05070218090703 72
    0x40705040341c00b0b0000004404040229100081080355250340c405c403846c0c4114040c030f00f9941e0265118501c0d605061000c1c0500900180700a0305146d1a188a41d094802c26031065540c50640e0782d55141b05100c8000030b154094084901c000c082c010040e02a4442421074903c016850703a1a001600b840310403a10790884107440d01c5001903850301c80c0b500e41c0304100c8034090100c0180c42d060020400750700a010030804290401d40b45280d8091018502480907010142030340c0110f01405524002121784018100d020b05c10140454040c3c10005112101c0e240c80c5d00c003e00200100040130340c07004010604a4200000703558194030403549003403284d0003002c0c035400b41d50810340c00420041485419400a40204050a80b9200640c3d8419064194141c2d480d409001c038001000492060800c600b0344d00301c1e04101a2003c03d00076913410708500c90350429001030b00c0244c580fa9010301d41134071340c1c131600b0380d50091418201d041c00c0490300402d003c80102c00c5205410403a22001c204200000c00001008540c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 148799757 1250 148798507 148798547
    0xf06061603081503070b07080310090906021e09060f0c0c030d0903050d0203070c090b0d02040c0309170f040e0703110406270612020714010c0507200609060901 70
    0x6180052041d0703400c646000390324043c0d5001c003d0354640400c140741110381c013103103260416609807600c2100b688050b01c40b03417030b5075216600001c1c0c03400e40b030150328845800358a005882c0c00d2032130203250015450304000b02c0604400c1000010340e5603581d040e03443c6c05c0303500000580c560010110f090f18040c20780940541c5445a004500d01c041d5120154000f034034481d0040d07a03d0845d94950036030344c0c0d00410400505c0002460800d011003601a8001920b1000c01440f114240c41e00c0d8020030210340807580180c4c0066107a4000320300340903611a40a4030b0b009226089440c00c1070340345c0114014022400742c041c101c0c00c0b21020628041c400d030401c491a409000d4800c0c1d417241e0f07481000e0414500e0200c100c640d800fc04070120040210300501c0d801b220400e0302d0380180780182c541100d00030750007668100c480d582c500d4561982d010003441601103027196030b12130303544d202e2042c100b07040a1480604124402c00f01d825002110303890301c0d1300740c4e54045825140f041d05c0700060001a60345901c02c9504900160b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 148801007 1250 148799757 148799797
    0x6030e0c0414220308060f030c0901030308090c01080603070509100306020f09120d080a0e0a06021305090610021c140d1406010315050d050f0f06010914040b0f0606 72
    0x201425aa1501a002c800c3c8403d00759110796112501c003000101024011a040b00d002900742d043c002c125600442000701925222411540001c00b808000e80082d00040c20410801103a00f000b0400d0207564107090038840d4162402000182da0303900640140360154000301e011440c0462420001800f4503485a401d549440340340c413500c07981ea0010820325100f0322000a0b2060b8a4001045c14600201076554424032642d440d0096409800c1c848100c080d980708096804c00032071864809412501c20729400700c140c5500e001d0801020500c00f420f00f9101d150f40210380008950002a04480c084d11100d48641c103410400d000e07286c000c5c207480043d0742050f001030710320001141c40d80000032820310b12038080d00c00e0b19a0b2004500320f5183d186c00c0c40e02c0c1032000100b4451860100036504c4228800c10072100d40c0e10182d44500d041004c0301e584600b040d8024801800b024025000303128420350007907081049813409484440540c02c0181c9100300f13070b00400c008105140c841c901120480200040011904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 148802257 1250 148801007 148801031
    0x6110d02090108060d110910050d0311010b10090e0606070f030c061109060714010f020a0903050c040c050d021b0d05040501090905040807170903120c100e060106030e0c04 75
    0x395020a102a0019082900060803403508a00349004035410509590240c0040000e012101034090180c00312503840510004450342e8484000580502c2a40e540c508045644401400d40320f0300d407012440b581c00321410001035540005500125641f01100801d01d1f01c0b88408107500c0c0c407400c07101230400b00c4c00180803400d05401503c1c244140303105003000c001e10342510243c04002d009186025911a008010714008a200712590103001096035000241c030b40d40d002c4121080f6030140e8208404244803c600700b0a0002c14041e4110300b400076a01480900983c00303006107284540346020300100d5000c140400021a48044102d40350b2031b0008541000390a0000542503400c188601c40c00070702450404141c00e280d81c000c541c06a6400403000d4105020b50340c03481d42d945c9000140202c013130300c1485046101d030380c20044030103400b0315118012303aa101642003860406034114040f0300c25504080011007003001c0004d0290440d103480c50000341003003e086005044c034048145a039032040c00c0c25070707281c2c0d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 148803507 1250 148802257 148802261
    0x908030708160206060609010f030f090b012607090c020c0d05031305030304051f1103030103060506150903060424050c03010f06180b03060604080607020d021e0709020706110d 77
    0x1a10700324001462040001008076904c000c04c0340c48a4001070244507004155024241c1248614418107003c075008046c050b01c04c04881d03540e5010b681c500010001080305c01c5001808820044070515450000c2c0e14203807a043e41c4030080e10804070850f9440e0700704070b480c0e4401d200d0541800320092000c916014a4101155203400080440c0413258112000086500e00042140e0482e500500b071054685101e41ea8803020b0013180029909000300a051590410014801503002c0c0d40308210028030303402c000b418082c0c40301c80e0800c02c440380341041007411526680081d01c2d80d4020f0303100d240003001c458003003040709022001c03086051040e41400d00b4030078144e420303002a50507a8100100c5151040c0d941800300c51f414240b8280007400c04030144103000300300d5400d0083da0f0011010341443d2503d0b0350b0b401c203d0315202c070460b549001070300100c84a4100c43c0e8107100c2c9660b41c0003041c0d91049001c40001d94503441e10400c2c81062079080d40002e4807001c01030307d500404c40b2604040d0342280c8079140300301c0c400c5c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 148804757 1250 148803507 148803511
    0x8041211060901060812090114030a0b0a0305030a1d0d02130b0a09230106050d020708120106080711010b030705040213030209090718050130060623041406130908030708 74
    0x1c000d016205400c001c0c400f40101f82c0d41e0880c4160b4070003e44091149003000c00740d00c041c1800c18004d40b240780c124119200c080c0554002c600c602c00840e03032078a00e000020140c50380e6105240121514040f84c094591f07441c044088810740444d14aa8034545c01d201703040040c840b040410b41c100c4286400092a40c1182c2c0c45500c0f400549021040c0307016070342c034007160506d40074081c00000c102c00344800900c0d03048a9000c0e1040c18891121145464100124281c80340c070264440070001d542c0004101110740e00000088680380c6000081c45800c1d8000d0001c0d444100710700a0500640d40440e003800a80c407440284002542c0282c154141c03030808a48403078036203450f40101000100c0c1c11100c0411440d0501c50395041390b0300f0441c0ca52040e1004030151b80891084040d9840c0954510a0800410794600c6480c008240a00059030000c2000300900e00180300e540505100d1450032804202c000c2040c484242e1010003203d403203a14019000208000340050350015144d10404410442c10035080300c0c0981c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 148806007 1250 148804757 148804769
    0x1409280501080c0703092d091e0606080601050f04050604061e0c0f0305032503020307031401080a02090405070b21091b0613081b010e0307060804121106090106 70
    0x840d850f603820a41107501e1241c4140100010340a1104010040383d003001003003002c003d18402000190094141590404560003002c2d000c0d03581c0109421095070b01c61901c10400c41920103010081c07401501820b46c010003400c09044c08800550801e40c02280d0080b41c0140200411013601c450319100000c3c84846070440941d0b8400351241001d102e1401510310a0000d41e000309000c0d541052950200d566410140c018540031b00b1504120900c2240c3c80c1d12030011a40c559401616072400640082c11341c0e8011004205041c010741c01848881000315195101c035130155003400b040d40321454032500d0511305902c403c115403004280d00c3d0410045c2d0b001040c0c0a5075170a806451612040009502c460010b4419500d54000420241660070b01070007400059408000070b080495440100c0c60901c82001300482201c1b0340d1102c0310b0703829138218140c3c8650141c00c4d0b0040c502030b030030318401400e03005000c2c0001e03000080f03140901c00428805c1707100b07050008001d02510f2581c1070481070180a82a103021b25 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 148807257 1250 148806007 148806017
    0x13030609020108180c10030b1017011d010911040e0708010f09060803030601030506013f0509120904091e05060603010c05090d05070f0b1c0c1409280501 67
    0x85203845040800c00035440c03114502174a141d00728401000180c011409042e02490b84510702d8100c542e9a42e002113000341c4041e00c4101003190314058412800c40305811400c2246401b146400c001c4281c0601c0314195a0191400907003444410343c03402050041e035000c030360651580000c201040b0340c0b003950706040f50105001c40c48a0394986800c04140c40c40390142c001160b2051001848a41c841e410041c0c0141c010705021510f003071034034040e80140c1e090040300c9607242e03507094a0450102c80140e507040e011216940070017070340c105041201c0d103641c0682c0041152070030114102c070035030703456900c410002680043c114102000544034000100903003101600c0381c1c011280050703241d00341809010060421540c5d13051420900c2070800030f42a4820308191518841d10b000458200740c891350b100003410f00d0490740ca480f41514190f00858602c102171401d01d580c00c0c02c0303145d141950801140f0700c0150600c80d03a1f5880391042c3c00814450711701807031291410404440c0200c1005006640c0d0000d80d20701303a8030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 148808507 1250 148807257 148807261
    0x50f16060207270b04020301060309110901080a0209090f060a1e060807060516050601090203040c06020c2d0405070504050406050301200f0c06150f010e0d080a020313030609020108 79
    0x26a02d0346220320985100c0d0710f4500c50041c000c00b40c115102a014141d07580014201451400b1034101c0e0800d80008010a541d0072002050049030440b4000e0090b04448484a96041039545620703881c03030100c024058480030b4081585008207001d100642840c0380121040d0340350910006000d0001d0030010700401d00c0030240081030b0495401a1070503501035900500899280c0a002c80d801d500155170704030321400090070366001800c2031001d54005c000310000962241014100791007400e42691000040d58411a00141c2d42e40b40c520044604000c085410034900c207140d810290612856040242d0161a0404208005c1d80203000760050318003e4a003045165142c42c2810300322085900c8004c2c40c046104007204051201500070100710000400312428042c0309070440303250900644908031241000800852542444a4840319940d02468560800e10301d00c40420380c160240c5c40007401098000455805540c0200112981d040c034640007aa4100d0b52030612000a00710804104c3c00a820800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 148809757 1250 148808507 148808519
    0xd0903090503032a150a0501030b220201081801090b0901060816090c0201020403050304030807050c01092103020c03070b07050c040b10032d0506030c1e09060607050f16 74
    0x30030b84482c02d6900e00a1030540d43c440b05000313810840500c00c90f10510405a00780c8004144c00700e1140030f0039207100041415411403800c81e4003204010198a03204281d01403020700b031048100fa5141c6c40c0d4082c00c0011090715496211000e40c1e03501183c0094560a262810f4100440755907c0c0344102180c00c020000300d40c944040c16198501c0b02c1d20f4002001042101780154105a4480e40c8580c40d207000051070981e80355a60350850308558001e841c9c2c01030100c0e00da01440000e1142031840d00c03003440c0060081c0d040007050542132000240d02c031901302c4621508002c040c000c115050884c0c000400315a485541e54802c4c00d80d69102c83e5003100c42f4052138417603020740c0c01d003070141c1040300314000d00e402210815150210001c1903402e690b40104011803080008000b0078009170912844000c0000c00d00b0301d041c400349844c0c11000c01d80ca40c0a00741c8440d81058000c0350325032400210408489401150b20f542d000515603008120b030140c024011040d0b62079218030006808211000c0280c115600c26560300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 148811007 1250 148809757 148809763
    0x3020c010207060c14011508030a09090507050d090c03060f090303061d0402010c0c0b07030908010b0306040b1501050d020a0e100f0207060305060102190c080c0f0d03230d0903090503 80
    0x103c6498049805810800d0000d02c40003021141e04400d000009000c4800f200c6807545c0d008260b0012200341c000152442502e94004841400792080602c20b0149041c86080100303a44903d03049e28a21540e1007070044100300e07600002c01c008580044091042050a1400d08003c0000705001c80c007181c5030103000101c82c1110390f1550920041c00b10503200c181d03103940055a41040212040b9201590003002003402400b00e030151890600a9890b83c20907410804128211400f220b0f40c82e11960050b4104800075186090b4940c0c8400d40c8080400d140d44003c1c01a078950040c80c00e19000a0300208100c85010760121090f6660b1804480c02c2c10041c039280d0003954000200e19107000107800c4000c003808002c2c0a81c001e20b820500c1841140c071074484008602060001c940d80c21200c00d80c081504002c1500d08001c0d414180004507403000c2d10081480002d9201d501040c80142442039a20000310540440c1c842800200d12241c943c90340c510074024110000e0210400c11000318050110209840c03c0c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 148812257 1250 148811007 148811009
    0x105061306030c030803130b040c0608010e060a06050a030b130b091003050c0607170a0201050f07020313050d02010c1a060a15050d0515062802120d020315041803020c010207 76
    0x2620b402d040390031500c070403055510080090004d0704070302455000080c0d035050740e80d208500421030b0040490900c80020000cc20681c0504134507107007142440496518900b0110885a00e4100107a40d60900d000c150090151032102c65400740324000e8139005101260400c180d80d0030308070303121b954a0782d0f8041d0340340c0b18514500001d4042c1d070102150540f1402e1800c020500103009010264900d440e0101040f0260b200d51820303070043c0d44031002e0040790a94001102c0d0004142d00140d400c0c810f0014443c050350300d161040901c20b40c040c8040d0029a4059074414011581200603450b0001104601551070303d0300303840345401009141d03000207003907500104281000c030141d9944e5150054920440b800340402900d6501580341c1003900100f0740d81c0d0398005154804414401c801200081c1c50342e906401100c2d9110002c3d50040084402420b0420044440003882d9a02c010b849460350381c00b5103850045e09910341e03049480c220003004005200307001c0e81d036060b00c290b003150035400504004986503038103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 148813507 1250 148812257 148812263
    0x61d09210d09020d12110706080105010e040911040905030a0806010c0c0b0a2001090b060901030201080103080a0e0402070c030b1b03130203100501120516030b13050a060e010506130603 81
    0x8180103076503031040320b904811452800240660b07201c1095444010140040d5200c480c00b0030301d0b601401640d4801404020002e00c00c40c28809a5589054000b81280c0d94106215108075500c807020b0041080c0074840c1d1014900141040003100518038000341d590340243c1c0c0f42400b060101002640540c032030b1020f030038115401703403500802130320302800c4030800e4000503016024007070510114048505010040010f010450001003007001503400d0907a640038000d0141800340020200500150347c02500c11030460368080c0945076160b6030380b00108d441505000c48107a006000055071818000d0340800c0e00243d074022008620140c8840e44400161880d41100c600004014030000c0c20841c074042011101030b0002e415180362641e940c0d484411980301360850388030203142085c52401d0260804c428040ea160a0040d0a480340c2980c45068583c3c1c0c004107005180040c101a40d81003003c28000000080e5201009020100c03082e810580688400c40b519400380c2c400c2210034030454401d00070002181c0d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 148814757 1250 148813507 148813573
    0x5010c0f021203061f12050f1006080c12130503040f06030f02030417090a0906080303070207050907020c090709030515011a160f020a080703110312042106061d09 71
    0x2c840310707000203c40c424018500a005211041d06c0302d241542c05000d00c0340000b8034032036a1601d0181d8141d14010328a4000c0402c115911007000403600303240b811510312260700159550a030f61034024050226a010000038858000402c002a524082e940600b0586100d41c4050018140c02011a41203010484010b0803403280c00262100a4540000501007400040d20b101d844a0300d5227404015125203601c2100c49900000c20031109960501010020300400c4030321409604003218001e540755401011144505038510114036001d01800300003009560080030f40c0d504035000308120303c01c2e610922650106040e214100320004900100711003518401541d02c09182000751128040b45010740c4081f03800c00d0a08502241c43e07802040b410009501c95618100d0041a00f002c0c10f042c202c4810307103000014400e21045c81301090150314540c2802401e00981d0b1340b10740d20b00340740c0003070300f956444246219141408814020003824007284100241000c9650a001104540c5001c000c0c4107050003031a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 148816007 1250 148814757 148814779
    0xb0909060601120f15030203010e0111120a06090e01150509091e0102091c0c0506040b09040b01021002041502300307020c0301060b0d140601020709020a090305010c0f02120306 77
    0x580940c11499460050020004604d484180c2c1001201c402100c80301094460110400451509001d00c2e0009400a00203020056560b010388180780911440c00c030b4845503110001d2901005030380014014102d0b003000b445040020320b001402070504003110346000001130400300707590a1070700078036010b0001e21000300000040700014000c03200c041a84506295020844c0030900d556480c41c3c00500700c0c203a14482200c0005203000c0d0f442d4241c507400103014403401c0c042040308101480c140c030481c40082d05c0218051500c240101d0414103208440300360b980c800304020411a0703640c00c089602d050300390200c0d00880c0c0b40450003e100c040540e100c5060301941e054080c0740030307010009550040aa17004442d50b0317100710700010303007034130b103d41c10210341c926021034a84050020741c05620468062800d1341010b50818400003900c0b000240100605d440d0001031401c40507108040041c0116000002004002e8903420000d060103222281d0800505c0b0310000c1a176282da01300200c03805554000c0200b0354103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 148817257 1250 148816007 148816009
    0x9060e0607050d09020103090803010806010e01120507050402030403030b0901230105070c15020304080a050309010f050703020a1112060903040602160f0e04030309051b0103061a0909040816050d030b09090606 91
    0x50020544c0c100e0400d6100c82c1401d00003440440614064128031003d402d1a43c1011400d85100070305911052400040c01082d5010510100d06041515410380700541d49681e1030500b60090700c4030a0300b4542004400700005082c0750468910654114403803099000c81460302d004680900504034007600100100c0c408205061041484241110b02c0f03005490415549200c59402d02501c840c0a139190340000440304841c0d80d001e02d0788a0840b00305d0800f24145201501c0003540da0601200c01808000040d01540c50707a51000b00000403070114900700d84251605580040d00da400a10880001d4400c94469640800400c4d030281e050340c0c0d0368040e8195003450f1411038008031401074016028142c0d54a06403012402c10700402d0100303600c01c003403c0002030110b000101120b41c681c0c018081c0300320452403801d800380000d04a03282480d04030344240c03040d00c4d42d040c103402c03900c221900c0000d00c5c220001200704000001c50003032070180403600d0400c2115034407018032002180c1152050030a40007140044c0381 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 148818507 1250 148817257 148817261
    0xe1b0411090a0504230903090f0105030705120901060f0b0c01060603020403020d120e060403111002013b01020a020601030303140106054005090c09030d050a050f030a09060e0607050d 80
    0x3803010718246082900c2c1c00200a05c0c002981d24001c507801c00583c0500c541004810504840000e02c1d0151840c605044001c105000c4c6c1008811070502c403001151618000750000c00c007070607840c101c1801e501c1e07845480e0120340d8840c0700b4010b00d0f5400c000d80003a11500910946046940103415040e00e807080d03a5404040300c0c4158101e009100c0e041030888105c1d240c040150000e0361142c28010fa402c04113504001c0e0005046c4c100b1011681082d011003080c07003145444945400d0180078244403410710034100222110448040c200071741c408100a07805540c002441d9040724000c4e18104804190840303840381c101c200740540c0001c02c03800c12541d40c500d04101d0030220301640008100940764030450706800d02050b010161301884620010a000303514001c46a26040105180b2052070400c1500209454070b00c2d001000c02030160108604918500440454548250750340c0036030307680d2400d440b00400800201500b40c0d61580f4212198211300400142e05000d0070b19a1542c1c3e050040d810305443c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 148819757 1250 148818507 148818521
    0x819110105040809011809180308090d0504050f0f04020a0206010e0702010902010c030819061520071205070305150a1109030703020f0d0501050f18060c09010804060e1b0411090a0504 80
    0x101032102c0c100011035901c1485107140c0c010900c090308c0319016090400410704a4040c1080700c298000c031110141550b004000c40d41107407010345003207116035079520001d490004080d42c0a0b40107800090651601640840c40c24182d500038040804191104201242218001d0340000e010400c0c481412021034080c640c4a0341c0407145a0314800f000604c101110306595103940404800070341100800c0000703401c611091f0007203240154444404510503e4980e4420851164513101e045070140d03101444014020f42020f5a000002c4030354048a041c104e2020320000c40d00c228041f0b203080c4070b40c401c0009800484504400050080c03620508580800401c0258440c0c544d41c4100742090304000164203000d602c2c171a4007402c102c0a19890585a202d0404400d06000d4000e60400e2080100d4078210a098540090081c07804c100e4650700e5141030300007802d20070b41c0503420313100d007004595510304400500910048250f40078881c1843d178040c210700c10b0040d407102c41d0740300c424040e091006003080e5124134 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 148821007 1250 148819757 148819787
    0x50c0d050f0c1f2409020304020303071a0106090510200102090d03030225050a1104140c0919210f0206070b040605060f060d0513081911010504080901 66
    0x3803401e480000c01c54a8407160700180b0784030203e40402c43c900a11284980c1003014640d90b2601c400055041c000c181c8000180501808640d01201040c15500c2c20420b40f18400e52014000c100c3c00303130000c03c440c6421001d1080100280c0e08100c046114103101d12001d19048407619298545500d12640da400061110a8140c2030b40d400d21030b40805503140e043c1e03140d00314002d40780141d803246950907800b0034500250300440b0304804161108005140000d0305011150098291441612240000b4000c0d12140b2814003000c89001c05101440d68050002c12509204403560700000d4014070003454100c43c90311a1214001c80700e159891052101d108040509100e504c000c020340c640c03a070001d410b0780c104003005c0c1e07003089800040004020b46072054540000084612180079084100019007034801d0b040f55070121074481c8040307036003100c2c140070912900d40d00c40c901940f9048910030b0500c0c0c00c0f11039408030002030f08140c007500f40b042041c81490301032604103406030316140c0700e1001941c4081940d4628 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 148822257 1250 148821007 148821037
    0xb01050316022a04150302030c0904060f05010620150115050d050f06031209060304020d05010b030f030a0e15030402061e030108030d0501081603020f06070b1003050607050c0d05 78
    0x16880c4410074400d41c3d000307092200882040d990009042c00110342d100c44604508101550060000d643d0016507440e1142d030894008216a6941c40c04a01602c040c5850045103801c04d0001b284641d0010682000c1c3d9040076802502c110f0481001559841204131211031440c5550040c08911540c0d2500403541030300307080041c035200d650740c40c04085580485501d062a207004c01070010230716040c022058a40041001381c0e08024510000541501c8003400081c800d84a40d5500410404290460109000020300b900c003403145608019032a83c0c0001c4085000800e084000c1d100c0d490051204000e654000c24014119038a0b81e080c04821ba10900d002d003800d1007643c490840c5c4035507540045000c1c05214003d1500e51841f80e4442003510701c1078006c2d586a410034880c1d14108884c0010070780880b60100c9403508041c0802001c81d48a21a040c4082c00ca6192081000b0486c0c3c3c09624200440c0e05c5107041f9085542c484c40200c80c039000700c1000308001d4001580c11300c513541c890005000880708199603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 148823507 1250 148822257 148822273
    0x3100b091203070b1503030705030a030510080d0201060e1303051206040b0a0602030406080c1207181e080d02060906040b0417070321020405030703030809010f090c090501090b0105031602 82
    0x1071030301d1900b004404990100042003001030410307015108a403403040550056003810065503640f5220700684150004240e580c2000480001c02c02c801d100051100400356198042c3c0004028060649c0c0e0190752152a40c1c180400c801600403450700201c1500359882c1d0341003150840b260116800e01501c501d50180c0c8031040c490300d41c0e690f59081c1c00144016001566918a00701026140e0f00d4002c0c240010340c0001c2c084c900d00c28102410a5031b1090691030407080c50b40403841c6d480c06c86400d60300a6120310710051415140341394078031000300a03200b2181c02c0b94846a40c520003266144800c41d6a40400c0c0c22100200d4001040b0000d4103130061f22803081d0700b0522003e860502c10341d410642041d03000540d0441164070650100b5078648446032151002c0d0f00d080e041c200031940d107030440e1000400b000181c02c002100303901c0030b500288413041c3c400e8040c00700395801e00345620000d03040d0081501c4140360900010300f4210702d2007011108a030684072603003944e84810b002e81d664246c820801d019401030840c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 148824757 1250 148823507 148823539
    0x3091012060329060301020304020d0f0f050609070501090503030a0c0320100902040518030a0f0e0303030403050a12060f030803062e0906020a15020c0a06020d0501051503100b09 78
    0x2620b072400140f903e40080d601c042e4450001410040c0c03c41d40070340d2041080c44056194241560003540d00a0390800e504445071924441d80303840751101030b02a00520007442841000852014103d5500340e85240c000c0d9110010162a032150001d21804203e89040c003800190249421201c420883c040c07800b115101c0111440c00c0408000030724012555039490f1804504d01441802c4c1c010b0600101c051008d40700d180399039600d1180061110a00c07550500c205407003480741c0f1030084130000180949489007030901d40036246400596100c00891000282c07100c81d41d5443c8100b078102ca0055048c0354001307242d910340041660000c0d0180c0d401c039450500c0b4411131018411100445118115504040c2c0240007000382180c013181c210703e00710740156000c84041a07120072503c0282c0c0c5245801640c40c6041d1800d41e1030708807200001450f050012074030031400035a42e4030150403541c041d182154014000000015180320031521500001c131107103021710942a078940581301c80400500308480c990707002c02d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 148826007 1250 148824757 148824773
    0x615061606051e041a06030f0109050c03060c0f0403020f0a0506070b060f0f090606031503060f01080d05040602030a03050c1303060617031914090a08010e010608030910120603 77
    0x9030040e1901c1e511402800a4015020030380180f07540082800c0d602428079503150000d166070580c00c025203001c1100401c0143c0e6050010701c0e00356004c58020011402d0300d1400c1922a807800000ea80b00380214030000e581c40c406003085410707000d0a080702c145482e045034204010800c00c1c00074143c000102d01750100d00d03526000e00401d00030740107042882c014a010303000c020040c404440382c80d005104182d4651078584540003d15085071040350240d17100eaa88624040790389624821541c0c1c544210400c0c4403084010703002441c140c940200903111020303004041943c49100380d20803407005038000c0041c140d80714481c0e880786400030b81c5a115a40350135910b101e0043e4220094105940d0380c4c0d610403003001840c038040c02100744200360380e02460804100540741c0800401ca14081018171041d050030b40c0407030414404481c80340720000c0c40ca80203503840300d840b03500801c24800618101d610345080490162000000c0c0e5040d401d0060540140d05c019100854624103060f90902c0c19507103039203000c80020308032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 148827257 1250 148826007 148826047
    0xd0c0b19020426010b0604030204090503070c0b07050f120702090712060f06030f0b1804050a0206161b0803180a1d060a060c05030d050403020a020d050715050408061506 74
    0x1c1642148881d00c401c54299500b4105075000d015070f071412a211704240c65071400d03981240d8044500244040d20750924a08511900c00c2c024030400d503110021440e0034410000d88a898010f004845600c100382030000da41e803e0f11880f80781100802d2040d03e0043c0361801c42103501038020300d420003a80c03074075990000c10780d80290402c09078042210303424000d00f581803003120708038021001c060000503d03507001b050034200f00554040920f9010070000701488010041c2284055014110b07a5942d0000519843e11b2841c0d0001194001842c3d6600a8000f41e041c0c1c590095078204009186000c080d940b015038a003880d000102e4103c0703501c0d4800035085100d014941d1001e460000c0d20782c06031400c8c3d0308010030700c045030f008401801010107001000c03a800000fa14040001c25100050f1506c460070706a260211158000790720100da003105400b001400304103581240c10000307000802c0d444e00c0c3c106803482e0185006a5503a548200d0005200040c2c1400840d010600600250b1401d4000c2104140710b40d91 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 148828507 1250 148827257 148827269
    0xf02030708100c0203120403030b031203150a050d02090c0d0e0a0606060201060503070f0e0c0f1b01051e0609040f080d0c080112080a0f051603021e0d0c0b190204 71
    0x100c1d01c260004064051804060f0543c406189810080e9803000503a03d0090805002c150303980055080316102004071000088840c05031070f841c3d142c2018444104007a56120500900d00064009030608082e1303c3d0010300c0364000c0901c006555101c840070b965030081500d40512a0300d0f0049010074080a220010f1150f000740808140c09081100103802c0d00c6542e8003650095200c44010060140744600e0700702518010320400440ea110310b800841d547c0a95050844840c00c0020000c040c14040e500080a6580620003403020b641c64100414894102c0d88410350425003400004210f454601c85c1c182d0721034420750041e803441896440300d880a4105080c607410607690741926010700703500801442d004003228121113007070501c00d65941031540078400613a01400301040f600c00500b800f41090f540c083d4940850654a401d040c10002d580700074403041c050190405041078045945c0200c1c5071500d10200c0c4d10b4a07440ca0b5003aa03200c5030421f0008114982d1400101e58907074190500d400102b0040c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 148829757 1250 148828507 148828513
    0x102030603061609380c0706082e03051c1404060c080d091e03030605061305010507031206060c0312060608070e0406050603041a09030a050d090f02030708 68
    0x24002041c14a4182d014024072080c0040380000d07405168040208010f40f602d0301031904000d0040c07403100109040c0045000c210220100070008a001014050f200c40c10a80b003c07281010740c1e030881525007802c16900002d010300155080c0101200d2103031039003030980401c060311940e60f650b0f490326402c2c1264214011010031007420b6624020b54000500d14526098442c803071728180c540701c4040d1807075680000041640001181c980141c80703103540711041d95a00078000c2c003044203030130038050b004079040c000880c046441e280c0041801d0900000f034910012514400c500700509240043d201900059411420080d0021409142245e18001e240003490952900e104e0110a441c028219000e006090341d106460a94104907065008001540110031400c1c907401892448000c50081c0a040c0c02c00c2e60445000414041007210030800642c0d8200354000203541c0c1e0300c6442425480c2e04c92091203200141c1c2c02d00100004a406901c9071840520a0030031006690542e40420706082d859803003011190 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 148831007 1250 148829757 148829761
    0x4091505030d05041a090904030c060b09070201060812030c16020d061107110103140a0e030403051204080d050705070b0d0f092a03020306010e060102070308040e0106180b030a050603120408010203 86
    0xf4000d81409040c1017208510340703042c060014007080840d00000c7c009070401510600d4002804090b900000103030102801e00d500600c0c0020029010f41220711421015201d04402d50052032071500c1a20b008180d410003032845c01d141030285a1408000a20690b0b000710040e012400082c41e40c0700d440c14450381e50722101c0d22402c80f82805900c405103203541d80c1c1414101b081610803a440602016071010f400480005c040440d04212480e5000300d0f00b0080451081486845e40c0c2c030828801340040b100104221482c4600a105c102c0f02805034a200810310340c0880740c00d00641c115403010780142802c0c184c002485010306000901500e000400903154202c00108164084a00c80a0080c2005070000c0100c802459940401da0711001441811400d03400788010074150f078424001c5600540d04071802e0b0303407110b803a10780f0412491020310606000c600410710411144040380110320441d8520380707401e42541d8884405001810700280700c15814026a0b440741c000510010242000d4180c035400140c42e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 148832257 1250 148831007 148831019
    0xf0d0b01080121020d06111303050c0105090306180a1a09010501090e0309060f070f03020d02060106020d090e180313030b0a0e0703031202040807030b041b060504091505030d0504 78
    0x890181c000a0103440c010a9003405007016400044241354181c80490f0302e900707281440c4000700f1401d80201400030700001d201141d01701c000d503c0c0f410b9a001e60142c58040081100568807441440d49464051b04180c000850415440c640da003d151301140c142e1310760350003540e12040e260414180c02003d02c0704070814006800000d00c40c0d01c0c00342a803050100403280c140300c01155203014000c10b45224000001e1b1000084582c2010707190882da0103194005803502a01e000703903c070b02c060350b085401446000000a140c0b440000e40f0350035500706844000c05c1c80e00340700c002001c001740103154010078840942c0c80380c000e40c0200b0081640300f104040c000b400358114a010300e0240340160503201018201034642800c1b000c01301c1e072002240d901d81802420b8a50708070118010740190b42c00b4013198040e10100009121454042034841d43c400c1c2e1826118107014018903c484000e0301501d80080c00c1800300740a480c0d2103602040c4400841141c281100b035855002918110f000344c81c410014401040030880 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 148833507 1250 148832257 148832267
    0x140103030c05100c120c030f110405180601050307033305190509150d0b0106020a0b1e010506030a09080f0702010e0108070210021309090f0209010501030915050c0f0d0b01 75
    0x40360807038103014003030402d002800400c0320440450003170903d40e6a0580c80304803402030b4481000d0040d40c4078144801c081d6001541e40341e4100f8810603001e140a042c10481003040c50300f6045c03246405840303007811515188001c5004115000c0100d00c00581409043e03811940503865111780f020000d4031480341420b140501120b01c840381c2e1510841c200c3c0000c14001980d03161552907002400207800e040040b50100040c0034070900740005000081c48200100c0c4455001c59811112800b81007050419280d01000d030f8581020300300d25460642c0804010b00c51407400c28010350700305c410010082100c0314603071210000340c0e1000200d42d48407800001e9980031540c2190781c82000a4090901941d50b1900030006500c9140b90a0031a488587c0001c005600c0003490001c1d6000e00310004040140d003c440c03404002044448900b40d1113210280000034a40d8864061000c101e41d000a040e603094441085050180c4000b414422805506011124001e08598060015251038030360108402c0040000505 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 148834757 1250 148833507 148833523
    0x60c03010e150d0c1a0a020703111f0504140a0302090402010f030f020a020a0c0f0e0a0504051c121d1207050304051c1a06060714070e010909021f0c080c01140103030c05 74
    0x80c004c06d200c102803180d008140d540032250092025850420311100058030a281c0c2000140018481442604d05c03592050140c400d9488140d48800c00902e508200f0062211a100c000d40c000b41c400000790040d44500a10f00d003200c0103090204059840031800b10580e0030490340d20703005900c517081c1c5209102003580140d00600c408100404841d0408055410440c0014894180c1d5a240d42c04101040380070024007035180c0000c0050940040003131401031240300c90340f1001c00040e0030600c020040a04420a2400320310180340102090856a400c3c822032b40c01a60b02503400b0b01003030000050341d0303d4031040700a1001f40c400d00c0301100c90091418200c03980310ba1081c03411035001201003200c20b80b20b090031a082d0a0f04480d910b40c1000f28000024a846450f41180c070140050000008000d81c03281c10506e500d610888060004000d03214001c2c0c4089030583c988800900e1740c001c040041007100d8020401000e01c5000451906205c1ca8039000c003a030b00f03a0080300090111881002440347c1070107070303038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 148836007 1250 148834757 148834799
    0x609080c0309180402030a0201182408070f05030a09080702090a021902160e18010f020409060504020c10110d05130209060102010516050a030618060e09060c03010e150d0c 75
    0x2c03e400e058000c42da6400c59074100a0501130600218000482d40c0c1c081a401003e280d040a0701201c054000c0b41c000d80f80146510300850002d202152416010f017005140700c4000341d46007400c0d56683d6800c0c2c80900090b601c240e641c028100080340c00b41c0c032910065031041c188500e0240e84d0740c0d2035520b01c2c09420700484500046422600e85c44d5103000354a102e090860340da00240c480a52542c00b00e03810305a500b00412a0158a0b0000000b00030b411600a0000c4410300c5d08100701003a52202440103a1103035040e840e80c180c0084031440d480c1c0b800360340002d450011030504603003814400c2e03c08404a40081c0e8950080e0184000d00400b1480d1812103180c0c443e0f002e00c02400541840072061300b24100b901d400800340700010030355030000f038803e501c400020b05c9401043c4444000141c5001c0003488640261241d070214940051140303480082d80b1800b603410b106070a032035a86058800711840102404d2000c07407180c4086002d20350f941d0503050000d203c2c01100d14020031071414505058418101c5142 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 148837257 1250 148836007 148836049
    0x80d090605040308090609130e010516020a030e0402030a06030f0602030f0a06030b0a05150a030b010f060e0130050411040f11090405150a030b1501080c0a0c0609080c0309 75
    0x10f0001500000544082104c1078413001d0300c881c008000102107104641c008003440740740c011889081700054221501030400c51b6141003450341d121404a031520700c5810050302190318000340340014105540195440070084000182064803039903465110592400b0549080743c012042c0980d00000c2c80c0d000d40c10800340c1d40b0800099186507614040c416004000e400c0090380c840020b840b12001c5041a101c002d0000c001d00c1030300d070712071801c3c0340c1078034081c01240a0410140130205119005d00340030200044140c40e20100c2d605101200c0004051110855501c82c82544005240701c55a0083c03c0c06240326400003a102181101030004a0b1203103100b01c01c045003000c10b034a41d889409000c4440d0780406a40c00310b00c81e500c403048811030491f039401482e00500300700c00020901c04403401c600d0103440d441d0415501d40c103002c0c1c01103031841816640003280d91000c100c8100c00314002c0d0075501d28513208900101c3c0406a64540d5409a042140b010280303410016580f601450403015190317140380e084500c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 148838507 1250 148837257 148837259
    0x30c15070c0b070f030608120406080f060d1b0906150f08060f01030209030312040602130806060a121407030303021305030102040e0109021b01050411041803020a17070606080d09060504 81
    0xb4003420071000350503101400b101c8044d0400983c401e80003940034200320801c5520f2480050b00201a951042c4a241e0000b0326640100710f80f0300c4104003490103041c0c0180110b001d9811521442d0700300c940b001d1440c40d05c902c25100020220305d82d025200007440c554032000c0000d68001c01c0600061044450304080004240c100402c96079030440c886401c40742071800589a213640b5010070700d144915007002c51584901d6080108105103500102001c4100f00010190300c0c0d0745251a55031450181c030340342c3d400031100000b03100011b200c00c03502d01d41500420300e8503406200715000318200b107029003040c1c00003500054110701802c0c1c8004000c1c0108002d5000314541454070610b800201818014444440e400041140c1c9041c001e4100b540c0156140c0e008020a0400b4544036210007020802c0c03d000d2800c2c912a13401141c0e02950710f10b54990560050b1000011a40d40c0c42d10b00060014402c5003098207011400100302d25106041c054145e003002400c800c0540e08001c0c059864944c0600e081041c1040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 148839757 1250 148838507 148838513
    0x31d010507120c020a020a030b04021c030c0803070c1a06120c010509040c09051c1205030708060f0a120503130b090a03140102120c0a030b030f0a03180503030c15070c 73
    0x800504400e90035000080301d07020300100b05c0c14800c00c1c600c06503001c61141408802e01090040b0746005520889000943c0340041ca840c0354000035005018011402c01c201d03102c041401c4000556000f03040c0c0c90241407824080e43c030b02d1b840d19117169101c04010304c02d20030013000303040080c40030000e003440c00020f040c040140e20000706280b0660228900840d03c2d0410102124081c11502d4040e0900410200080440d100b400d1365000e40000706680c0c0301c14201407120028090342c11240600e489a9549201b640c610081c0090090b08100854111b5540840050154030361030404041c0c0d84114040c550b02d01071101d80d41c8852440e0b402c03000d0710a03003c11090010b56a600d01050840b54818040400da492250b501340c02401061a290f00e6880742d08100002108400d0007040c03043c0050f10208518280a42415500e8401c1120045158494142c2c140464000e1500e410b036212000020201a40c984000c0ba00390b4201d4904440c95600110380341070060400c00c0c2c007a038005041d00c3c109550040300c1d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 148841007 1250 148839757 148839767
    0x110306090f0c060f07141b060a0504170a0605070e011707080f090f01020a050d14150d0215070506100602060606040e150d0803060a050d08030a050c0712031d010507 72
    0xe05903c0c410400040e030101900d6400064507030300794000c01c40c600c02c020401c41e403076112541a03400410511449600014030702d001c10a0362441040b540c7c405081c50b040860100d0100c04100c0d135104507214100301c030400200580a550b204169603602e900fa103039500070014102004030002c0c01208943c0a0401010650124509902440078110a01c498882c0601d02e4100300d401c81c00440f0650002a0030158241c005006200003a5081403c00217103640b40d40d51400300400f42d406906100c1e4081d1030320780502d0074007204007080740010106a0f400c684401d43e25041d038040302085800c3c0d0001c10030010380000140300f82c0010b010f240040e00c01481c001e0001003240c40740d80151000d420200c0013044419448210a900103103015060394080c0314503061518945e00200c490500c5180c986101040c80d041540d29410b03039a43c8601d0f180d040d0f4641100d13800182900618050941c0000e000400209001c0e10840c0343d841141c1c1c40c0007689105040999907408182c02c20154160304020074440965841 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 148842257 1250 148841007 148841023
    0x1409010e040f0f12020601061e080c0d0b0a0909060b0102030403150504230a140a050c0f011710090b06210613150f1e030b070e0409110306090f 63
    0x440304410041c40f07280440080c803055401400600b420801000e03070315000503142e4107951040d10b502000040f1844500741c541c100e41083e400141d8083c01103190742143c0380150281c00c0340d10001186261054011a401500316806600059203e6240c0c9090181c01c1c0701e000c00b030b080c0a201542c40e090039502c034a02c210005003055010035030b4940c00101800541031040d4940a0105c909403800b80c000507240f503403052480c03801e44004070250841c1d0074035600001c3c406181c2d5444400740a8520f064800c01c4610010905958188a40c418920a0000300d00341460300c1106084040c0c07540c181011420170880c1c0b06104d055015110401c0b141c203190504504034803400078000d030403180640d2000c01103007403000c1c130a0400e450b00c1d0600c8505210101d1200341e040656506882ca126550b030b80345c407908000014072543c00618501c0044c02d0000c42c1c40301e04400e903c410315052911b10901c0722000b141c04c5031500031003642d542e49921807610a9203802c0c4080d540004a0340700803c0d500305094a055212102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 148843507 1250 148842257 148842263
    0x108010308071e0803010303030905010e01051905090c0405040c060e0a1809020a0e131b06050a1d060a0507110405010b0405010e03010b060d050603060109020408030912010e0a08041409010e04 84
    0x2031150581c2c071091000c0f510403d8164401c0b00c00d92207580d00d1801a024210300b00c0100c4695080803803800181205100e020300c070b082503002107004a846240c80030001c040140021900b80600380300964252030f14060385000c0da104416000005282c804d000b48012542482203104aa92020411040707506480c6560841b00718200020a03030660310018840c020f9603407142250140e04000c0013402d01d6040b64403031049009490202114007100707250840c00750103004441c04548284040c2448a124411711141d4400c0f41200130403406100c000a582c6800c07058103e0001a000107105003007000c034450903c0400005d072024003665042980c2c9624a0040f40203850411000c45c03c41e42c00d56900350800b041c0314030b025152559890018031320501a0200b202c0e01070283c4108800020900d00780d00c01c9030100c0c0c0611000d9410318019000300320038010100d60356101c545d00c85030310844403c8184410007689103d807c0c00b0b5642c52400c0c251031503948458842d00e01c500040e900412190031911065075002d0b40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 148844757 1250 148843507 148843523
    0x1107060e0f01050406021903090f03030b0a030b010308040f06020c010c0204050c12040503070b010806070f0c0804030b070206060f04021204110103020403120e031005060f0121020f03060f010801030807 88
    0x258100414902507400c00080c0603582030000340414080c80d680280b003c9a000140b0701c900602888003a01541c4200c00c00806114031181202c001c03030311990001c00960030080005c0315140c0d494841030f4941000b0780042e11a040c00080810001900d1907a841c0105102d0004c1d154009101c0c0c0080c200c10312640010b0302942d100c0b00011400c035001c2b02250b070031465407211109107003403504069540b500011000c072011280e61001007242c840c000b0300c5e507204820603902c3c602c3c40148480129168040140c086074403100500000c400907102e244594490382079580140a10b243c1030342040410095001046e0060384100842e0f02e080342e10713000f42c44e40242c01421100b400e441800c0128000e00c284e510150105141000404c000350744001008100304e412401c0328850030b11400a4000c49405541842d440300c141107040140754010101c12510005084031140203500f0b01c1d49140a0360b201c00c0c0c102295000010801c506031034040100d0891540c03e00e0321841da503040d41e94502c900d02c80d4400c00744c4259 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 148846007 1250 148844757 148844771
    0x9090a03120609180c060203040506030c07020109170d0305061903060b1203120405010609050c090d170318070e040c0b07170d050106031a060406050a050c0a050a02030f01110706 78
    0x1d403807504a0070080512820800010384001903520801e20000d1040358260341a580000f050361000042d58207a4074000d00103803943d1908440306150340c0c40786c00304038144082d0356000a812034460f83d56140862a08000d41100814010020f040b02c2000f010107120301c003054440968002110414800e0365440540042e060000d00005481120443c07200d907001c0c840055080d065140e010480f90040c0c6c45040244600c2c1e40b11507440c030548404a401e81c00701c1e2001e020702001445d009007010101ba02410898604051200d001c40c01d43d441219680c84118018150f0300e82c110042204038001c1030100f0504045003815912441c00313416500c1891041d90005c148402403140800c1d14900702e9030031450300d42d034501c500c6140c00f000d06403d102e0341c0d0100346088040c4c081c0305604900580031389001080fa1f031805042c9403082c1c4594005004d0801000014801d101041104004011510307005000030685200c6610406240650821381c200700369040c665250300c03d400d248192000141d2100b4007107112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 148847257 1250 148846007 148846037
    0x3030509061b0f01090515010503100c170103062f120403090b0a020d0e010201140402061809090c100903030206070509040e1c11070506090d02030c0d030e0f09090a03 73
    0x1c2494008082c159010301d4515261003401548929840703031141c0c0c180c50b0071a44038940c28240140905c0346039003680059038000105c43c02c42e8840300b01604a81800e00070017942d0700c04180c03044000d82084640582d50301c8141e00411200704104691003d4050121145010801d07c5c51640251980302440743c0500c0049400c042c060b003844130243c64184822a2185041c0100a65804014811002081d200700030040c4951041c050500001c83e030707000c88911900d8540c00d10145038130890301c032540e0b02c00c2c051a002180d40c400702c0d011302940181000b040b81c004200c00300010041c003140c410b424880380ba44d04100107500460691b50020690424a1301c500e507a00104018008920341803d5900a80780350082c1c00c0144110460410304a40e43c4a5220b242844510742d9012903004155120300300b8032140c241d501d0000800b03212548080c0035074410149540c0803c10318403081a044001c5511144151202d00340103550040041046402540c1030400f1540345890b100d4404d0040c08104a1407689400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 148848507 1250 148847257 148847287
    0x4110f2b0606122c0d0306060f050304030806030f010c03140609190e011103010306090b18030d050604020706020406093201080604090209070903020a0905011410020f061510090303050906 82
    0x500f6502490013111060300c2c820207a10f80e50038030b014401007442c1a01c003050152080d15514008810750f15034130b00d140c0719a1410f60368440d00800c030540c50300c00d0f80c0c03400c0d80c00740080c051454400080c4d1404940341a0142c5a10302091008066500646168003005081040c909034801c5a844050000840180c0b40e10034902600c290803121404080000001003001800d43c01040c01034003500500540e9200c2800008810b10070001d58281e580c014480f210030404980c1c400703030700880c000788010715140c2159500410382c0c200e80e00500c0030410380d60041042c1c0c1094080700b4000028900084d80094082400401c1c001e84040103604102035000066003039151507019003171a07034000700b44120500d805031000301121245d00080340a0b150240740040d4110300d0b0f020705410b0b038140c0480c0901030130620040c0503d00803240c50711310441c8140036401000311014403010380038078021a01000003110b110b080c0308048181c02d85190030042949420004250f1210a41d496201c0071605207584070860090a08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 148849757 1250 148848507 148848551
    0xc03070312020709020f03010e0f0907060e0a08160e09010c0f080c090a09050117030702031504020a031b15021b01120b0307080f15040c0504110f2b060612 68
    0x1840c2480046d51031081d42c001000b86041315880081484030b070707907101078a0103410000d1341d117925964040441403020b00c3c0540703050046540084c11900905560740180341c03070b100c0c502c810041020007801040c048445071041055014042d90004e001c6c607911004010701554417031044108114039080420740300d07410340080707410036100100b034582e500e038860442c1d1000300000e1080510501e04180341d4030024070b002c000e9400181d00100582000b0b8400c1c2d160901c007490060040740c3c46071920070007000041c400c3d07203484110082c1c040407681241c208040348491003203907070012080d9803005000c1c0c00c103400c005da42c000351640700b80303444540321001400481c05000c041280d154503001d08140400c400034000394028620b0b2084044407049018111114684482943e001d062000d1988040c8094205a08905014445510322924161624860060710341019403000c03050511100c01d110061060b8402c41070609a8801c00c0080c0c42c50004082e0480e000003200819450312250019000721000440b10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 148851007 1250 148849757 148849769
    0x307090810240b04120f12030b030706080108030d0c090b07030c060f0209031009150c020d032d11070501060b1b0309010c06021b07090e0601080c030703120207 70
    0x1444034840e0101c85000340c0281d142502030000c1c030102e004a00502005107000b207549804035180790a0a0040381017502806800540d5401101d02c0c0d080c4c006000010198140102d503a000101c082d019001c050424880b6803001040000c28001404001c1d40841180c0c0c4021080f0030019010785c02c00c0c800d8510394543d41c004c0d15100008920801815085607a80104c0e51068074100300711001e01d46028100e004074221b8541540c04001800304907d51580f2080d08180940e4459240881d038600b1002030b55401ca44e07280068101003048095550140500548441190761070313050300c07400d035042685102e05415000c04244d00d503003284603007501c80011500200c1c0c100c802800003e4480002004a60020480b05850380003500480300d00c210100c1510258007050b500c400741d459198072144041e4003d2030201788520100d0f6481d00b894041004010002d001101e00441c01c409050901814020164000917264001e05c10003032041d980800c500e805e4942c0240078000c0c116a03040c040f0724101e6107411803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 148852257 1250 148851007 148851013
    0x20312040603020405040b0618011d03120403020f030703120507031e2d050904020705010b10030c030609060e07050a020f0a0f0c14010c0b1905040c0e0601051207030203070908 77
    0x82400703641600100260b0710b00f62800d0101d901d880050000f5446042e5201c0b00440c00d903c000940356220304041e1b01180804141528801c140c0da00190400b20340c50042c05014100103020000c41c00e0024100400300422800b41240c1407640e01c482c2c920359000481c2d20100310000800d6000c25008845c0301c00c02c400d11420755014844c0d0400c018140c601210b07405240800b0b188012a214001050f60343c6604c042981c2e007a04145128003480041e401a020894195489101c68111a111000c5015a2095580d0003196121012074060112002500000b03001402c14005100f2454008006504a1003e01c0c003150366484089089040c00400742803040c442c00f400001406100040d600c12072824011072401e0340d4241d40b030203601d0301100303008504d5000c42c0c0c80c10008004904840b08641c0c0c00080ca620a4480c4c01c11800e0020880740111802c41300052403a0003441410314000303120754810405c3c01c080349001d00b2a811081050802080703842003680000000b8a40361203281000c0c0180303055011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 148853507 1250 148852257 148852259
    0x903031b01060608060d2a080105040f020405010f05090c07020604050a0b0403050106090615110c030a0b0a050f1b07030e090a02030403021b01090e0903041e031a040308011202031204 80
    0x2a01e018090301d03c2600009002d1070701040d0f10707291a20f07210590a0380103218586010b02104c43d002488101b09405178040010700c0b0014040d003017030146900c070b1481001a0701696500344104411194180c124150b0500320304c0040c007460311407201541c0c0289d0841d42a0351503d440303100041d51403040c3d030040c6800c0030036543c00040da4491003001d0020303288030300000d02c500c1e500c0d1007082c030031100356110314079620b00500100202180501c40c40c03040320246d0b0080e00c5611a1480c040383c81e00344616001c882d079828400403c065030599201d2603400182c80b00c070b209807030300b0000700242c0e00b000a0542d002c28003000141031010140103400301d011000004d84041014a00904078800a4004a074150054007443c18a00410000d020b8002e001c1001610740d03018050a01e1210610240000c01c0440030744002c00012030071802c010204601503078501c0340461103501310b2400985000c03082c29070007815219031081c00000303070f08450820b040d00c6002c60300a40e4400140002071909010350b007106424000090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 148854757 1250 148853507 148853557
    0x209040b0a0803030a1a09060d0201110d09080106090501050a0611190b0f0603060c0d0903200d0f0903020f04050703090605070e0f011b14031b03070201140705070b090303 75
    0x2440c030903407175180c0c20406440b060244519000100229561003000130001605c0d601d0a8054402c2090041c54240d215000d0b4500e80c0b494281082052004520000810031070000f0274001c150180501000c01d000035490f100200d00400454022130041c0074214108081d0724a003000083c1c0e8191340c115103520185514140300c00c0060003a261071001a54640c006641810000759083c002d00320100707603034a0000340c450280c0c018400b000c01101044000f00781400706510f01481540e1062580c3c000c0d003810310040381e015100150484651040c005814410005a0b03203420746c0820801c4261404211655141c2c401c40050407503002c01819a481c1409209034154011001e100c41042910b41e2200c54218078019900c500c007680c20030540d40141815403000400a980e1503081401c004221b034200060010f080150b210078440c8000254004150501550303441841100a0000070138090700c0d100301c41d110691034442c54015180810000540c0d645607890400403075000721071501d5800e4004619403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 148856007 1250 148854757 148854763
    0x30403030306050f0303070c0b0307200d08100608070c02270108010501051503040221070e0405010b0406050f09090c120a02030d0e01020a170d050103030302120108120a030209040b0a08 81
    0x4007443e8080d5402806440c030a0400004403054690000e8910032241d00d0205071300781d1680300601c40d40c20080101d6007264082c0d188649403010810060250802d002c105c4001404480002c117600d68110b080c40c0200030701034004207002e800038885c5c9490070410003203001048111480302144100e0010952150203500500d400c80c905a5030230300300a20050b40d0320b10401c09810308400e0b2104140008001040061900d0b0f521002c0c1c0769004070044041d07900c2502031a0400c41903920000c1c15041500030001000300a21800030740366004c031800c0202c0c60800c00843c80084080050901901403940801c5145108100a2800510041c0340560b007a040c5044e8030385032180202c04074041e200320030f01103c005008078044002003106900501d059070054561110701c07548547c06c0c10b64094200304440c000e11041c020640038601070740340560b41c1c8046009801112805900150a9401100080d40e5943c07102c0300301d4400c03525602d07000d62514180800a0000c082c542d1b92070750312040301034000070108004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 148857257 1250 148856007 148856009
    0x706200919050102100209180f04050d0306030305160606051021060506160602070209040609030f020c060a0e0316062102030603032a060103030e0a0b0f04120302030c030403030306 79
    0xc0e80d009240316880285404250799502a80d805070b08444000c0d008101294098500f50b03000821107151b40c2d401801407402e41c0c406441806038a11076800304014003808001d0806618000d24041050601d9070314018151300032602401c402280700f007500340c180035140c0c00290191200034031502d00c0544900019009504078020060040348196100700381000b5446104200c1d0409041d07103180c80c50712005030400c042e42007000c4840c10381c20300024000d41c6500d04150701c514030403c000211203401e800c0141501300790300d0304541194020101c2e04410b840e030b5410380b0044041c0e81003118020660314000703420a159040c01c814001200d44000403420707809100c420299003001441170072002c0101c1d00400340c0c4400c85499405600c100f003e1100130b205e105940c103d170601e140303071012548800038045081102c02c0c4d100740c0003c0d000c5854070f511480c080502d40c4c010b1040c12007a91400702a04410446800703103210303094100c1c03002a1a4400c0c98000c0c81150540c0703034005d00f6280d50b5912460080c0041c511 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 148858507 1250 148857257 148857259
    0x51b0114070f030506090402060c2521050a06020c011805060a15080c0f0d08030a05060108010501050a0c06051008060403090f090c02030d090804080307030c021201051b07062009 78
    0x3a04010b004643c001d01c107480c040c050140401c155542c407502400307081e901a80c2e9007a96803142d05034040841d8902076202da0507004171030000000da171500d125140078089203c02810141c600c2044500040c03800601d0360a0150300c05405a2641c0d038441841e03006151400002d6058640c03410350788204100410700c0c4d44a280880e100304042c06002144140020326030080c80c5441d400303044134030390341d2030201c18442d4101c10040c481c40290074a0f13626451990001c0d82c1009216407140140b094540e0400e2100380901f0013840c02e00d040c2000050000c014104400001d003502e56620081407500400030403840c090a00001160f0560400e49402840c0c2c100d02d1162646440d5034910128204d0994041c2c00070940032603008508001381c0c031906000a00d034881e8220b4a11a0402000800007000c1c0083c0c031380c4030300a1310780190300340040c014007070301e0503001c00105400d92600003000341d0344000d038020320150759030003104a0f191507051500c44000c1a10b0000c032170842407134010013140238071048024000f10320 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 148859757 1250 148858507 148858517
    0xf04020d020a08012c0c0d06020304060225020f093117040e09060601090b13080106090f110c060403050f0721020c0306040312150905101e08070303051b011407 70
    0x10611a1701c680b9544403040055019925440340d40100b0501e4020b140c200e40900300051802c02d055544c7c02d45540180b1125082801810a840a40ca40003840c0c070850103055440c100a403034500d4404aa80b035644c000b08a59814559004141184c580c000020107036000d03480b100584042584020f03240c01c10701c22000c20300442d0001070704244003c15105e000708010384508508074241a0b04410540140c05080c0c0240390700307000090150824040d000c000d10a5880015103c403041d2110015580340c04504004080d0401060703d0703400c0001035040d0b01030780610f07000c1e450312812b40031500707a8444d40d1006019080b503d0208807612502084414918249800b1102018292402e143c0c4075030b000c44024011900d05c0c00600ca136842182c00c0f00542c01e002411403240356449086403000c880040c0e076072044c624036002c424407005160720a90024002c1c1e0803401d80d03102c0d2400b00c00503680d6115020040800002041c0b4002815072001e000e2444d03550b0303400038004a40801c001c158500c00845035140055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 148861007 1250 148859757 148859831
    0x110d020f03180102041a0a02340e040f020114041707060806010c02030606010e03070308190306060c05060123060c011a0a06080c070c1706010312080f04020d020a0801 73
    0x501c05c803001c80300040c8920f20750320200c0f048180c4a4111603495425800350a2441d8140d69070160100c259201e0100c0c0c400c3e0360090b41c078501109008a070001c01c4104024000d01002c200e000501c40304096092800c003442c155035800c100000c0c000c90b84408200441d445804090382c3c4045844001e84085640351201903941c40b00440751200c40300c001a425801c0000400d015510a40501000c1075002c1c00b02e40d080e81d540d98400c1e00740c0c0c4c004100451b038041c94515090b42e0b1a81130040e0001007105180c5521004035a8440c16160181031158400000c0001d0014080700c107018078040e501c010040c0b045840349000c99846000e8102003004560030080b0f00003001192074403c1508040e178000e80d9440440b5603a0513140003036984100020390720790000c40b50025801100e20040e4403660f5000c03000d400154554138140b02820001820641030194034070170408040c4641c0d50301e59109404454180380034840d1b00204942c9030703131500014165403d0549581c01103800e24180d074200e1686441401e0a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 148862257 1250 148861007 148861051
    0x110f040b0105190302220e0603060f01060f1404030b060a061103041205030c06011d0f0421030e060106050714010207050a080d06091d010e070605030703110d020f03 72
    0x35511180d4050200d00140800b480600d00004201400082d900f8014600302c00101c2c040c43c0541c05c0b960440c1c550401c011309000c0e910070311140507000b1030103500420741030515880701d1510603014041c0e03c041205141103071f00c0803441a00740207e0a103c20812903681d0f81ca07420f19002c2c40b6021620180503082610b00055458440c07420400a914200c0141d410207080181da035003040301d800d02c181d88900c401d0204010445043c04941e0007807050103901b0b10080008141c0c1c80841000800c040c1440e0300000410001c900c2c9171100b050b00080c5d48400a0b040317001d00e4025801444020218421407081c50b001180682c0c0020050401c20301481c2d4040d101000c0c171a0180c280d01c50600014400d82040b00c0800000320032002a09440c111650041242030b2a00304a034103c0d580c0c02c80c03a1444035042c3c0d0700220f056801317101d50008204140054168141400c001810600c409082401019981d01262402c403003c1c505607950311103d080155915035070000e001000d80c00039240c50340000d1120501c5102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 148863507 1250 148862257 148862261
    0x309060305070c0c120201090b1201050a06031a010f120e0c040b030715030203180303090607030513020906060f070512030610020d09030201030203061224070e0105040e040519110f04 80
    0x480ca901c844413150311810010a030445001300c01d0100e05100c040c0c0c0012501000311400760190038402c0d045220298036000030480069915070250080c0740ca0144110707400051074440c048003440038208429060b0b100a4101c2d4a00c07840501000c00c10f1600c4201e2564010106141e0705100d0203d80c2809101d442c40c08242d05d0f42003612400280c0d030660400c10000781c0c001e1700610303840318408410300c030b03021005c035200c0e42958011a070320003283d0889010042120341500c103080e0002254000004101c0740c42e400301e0030a030300240603280706090103d402e46400c810300c405c075001c8a03400f9054400d600c03040c1e000f000c1c03c1c0d0410740fa03442c411200800f80801e881e200043c02d0107980401e82d03940c0a82c0d4610340042d07009520180c5020307000944040d40038031030b46e41040320340c40c81c001010458824080f20500c440c146030002e002103003040700c100c1d96520281c1c1d00000342c0d010f07100e920a141860f501c8928007940f400140e000c034090007c10014168003401844540451758400a07690303034980e11451420041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 148864757 1250 148863507 148863527
    0x105100501090e0f150307030309030b01090b030604030e030c040f090b070c080307110c040e15010b09030327030f0d09060302120a02091302030109090203010f060503190309050d030906030507 84
    0x70b2a0034000000d00307007801013060103400214114140b0050107541c07000c02c0c10320207107802c168042004c1d56820010001080581d6006085110041010850020000340c840c180540040c040000307140056018bc0c0c1c040c03188d00c03403090f0005d000304070030018180020050f000b601c5003960201e9038140081c0c0040e01601d04500ca842d0b0149549145030345440056072284600d81c803c40c0c051207801e0417020251950312821210305250350080654688024004150034030582101c64244c5003801429040d032000425140c40c0342903050b4000015203216a180005c441d0703001070681c148240c41d140c80b0740130400304403a040c0c60215610503652035110320f015170a82c41620710602d070420b0130000044036030700f096015100d48107000303000441d1122060101800e136042030700210341c801d50f58002c800440ca02403040d840006a41d910502c0340501d0400002e8417480300d080201100c080d42c403452800c05100310881009000000d005120300a900e0a000b4001ca00034021540464942400724084c94000c8502c50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 148866007 1250 148864757 148864769
    0x70317130504150513090519050307150614100f05090d0f03090305100903020703030c02030115090e0d0311070b061305010305010b011713150f0e010f06050105041d0402120609010510050109 83
    0x1c001161840c10129032004e4548089e04d1a010920400c07000030100c03000c07a045c10b2010440850034a0501c80c030711020901d002001482407010780071905545420011081c110003850424540f42d0b00042c0c08199003988810f00204481c502407480e100301034100e20801c080d02d00410480301030024660041080302c00080010340941e00c00701d81000082d00c2051080c641d14400350000c681c003203906852900c00341c20364000001c0c2680320340020201c1c8000b00943c0e10703070350021b14040c0243c1d1031501711150540300d40c520140c410440e4100050590700c51003006400c00c156220200704540c0d482c1005030003891234a10039800036840310700b081d04080310418514006c0c010038000b1410301d100341c0e0f141c20190b001d6401c1d078244a9140e220901031a480c038409c91010303941c100c0003c10850300a6100e03000712889a0403e45c14000d051005002410079110002c0d60703001c0e1043c48607055122800013800384140080e01004904c51101044003d0034190001402490b801c0c911007012511a80150b9144200c0d0085c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 148867257 1250 148866007 148866013
    0xc0306140907030b06041803030605011103070b0c0702030c0d121e051c0e1e010c0503090601090b131d0c0411090103051b040308070507080703171305041505130905 72
    0x2403003c0f84030f011005810203402480018006007c92004130003000800003907000c26030360380c0e08104958100301031140101540c40910726001c600c0d40c4110300c500029010043c5081c2c08519003046450403c03a4285640000305485a283c02c0c0745010422800c0000c82180000d03051312418921211100c04031210440e141c84940c03d1101030b110203a40d01c50040d806240315034554404941c0703120140107038107071310302000380144214071440101c500356041000e4100800c08100104242183c1c0401c8980c10341d040001c002c41e4a01500703001402c0c460307244600b4001070b840e0036140100000304260001c050038000d42540c0300d00300340b942008111080b00500b41400b800401913041c03958480c1e4001c0c1d60240300c008a0907400880f441300e800d0141c0140c0c004075a04800014020180305003017041c03a0081c0081801441002d080d81d580491024000d4641c40b4115000f1512400d860b130344580c803d019100141081241c0c1c0b14900c160320429000d4171405005a04044503501504017a01801c00c42603003003002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 148868507 1250 148867257 148867259
    0x40504120e0103090206030f1504060f090b0f030c1002010e030f03040210030c020d050d0e030f030727050607060b03060702100c020a0b15060d0e0d0e0d17090d0507030c0306140907 79
    0xa0105400201101c40c01c000207050603840786d0301e40c0300d40d1000d010382d1341c0c09407655410109503700321b0f801001030f1407040c1d02440d00b005407590b00003500050330380c0c103507201c42502c400031800340c4c0036001140b00b540460001050003404070603060007440c0f18034000c640c0303a416880740c0030f03043e02100c002400c420016003103080c0540015004400408089040d101c00149005e422072a09085802c030702903940d0a21000000d001c8616032003100f040d4000310f424101174108020f00009001c0c0e0019102d4240201000306840080c80f078154040f00e0040005805c0c1c0d15103190a9000948640351140081d10301442e1521482040c7d20010320350510a520041c0c10905407034500d01c609540c55000b1099a1140c0d0400020300710070a030380142c03681104000b008003d04412104003500070503c2c602900d0055090114400109000041c0048180300d0250711650b00c980c410701080700045110009070841c0304048000080001d02043c0c102100c1c0181e100708280001d02c881c00c0121002600e1503602c40c0e000d040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 148869757 1250 148868507 148868521
    0x2220930050a170c03010302041103010605031902040e0f07030e0c0904080f070503070f1203051603150b120906070c03020706050307020712060b1008240f040504120e010309020603 79
    0x8014094080d281c03c2c020161124400e940b1889101141d14002248020004108600309801140c0c4440c2030074034041d04540c14850300a1080c000280300c050031403a0910117805003103c96040b18080c0114141c0d990b40380c5860014800d409109440303100010740380810003071603420089036189200900910442c2c0c16165922000d0040d0030000c000c5500220402801e400190100b0003421703000e104900c4900b8868143c1080000d801a00030090103142c10181000804106030000880c000e41c2c80c100025000440c0101030600032058006008203140041c42c099041503800e129031090344840111041c81d520008215400e001095006001d607000c00c405024090140001e160b110b285841100c03409988c4545256003007204c960203450450fa01e800303004035801d001e4a10714007400d06081840840c201000d04410001090f40c203c00c2000007243e000302c165031515022540561300810034001401c090612001603030080e880d08010604450103a007065000e4010724018070b8006009074195a9101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 148871007 1250 148869757 148869767
    0x1303030c080408012919030b0a06030203071e090c080402061e1602031005150607031707050c07080c010c11040f0e061b070c03030c02220930 62
    0x1111114400d0201142030102440303031030341c43e480010560328450702818840340030002d001c17003050051b0220a8011506004c94a00e0030499900c6008049940c1c1e445003540000c1489400080d403601610200090100420160b6943d1060f02301000710455981c00b150021984990303102d40104401100040151800740040c005a604003a03944080102589120340c2c10b03070010142200306194000302c1c0c825410200142c21064001e8801004a41007045000b00410f208003803d84c4a81c0000491008161050604409001c80020042c505003401c0101030000e405c01c1e1b1700c081c064820004001400480010001d030860700607126a01d00300540d80350703071419103000100b0355001a112005219912101d2144003a07914080740546018240a5010743c0b0380c5003940d10140840409000c242d000c5001410b5100460b541424640b8040c03000f480031030340300c40301d103000604001d03900380c2d0a420b01403d5030080c450b000c4c41080f0509132043c1c00080141c0039800b0a4640d5041540006110350840c090303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 148872257 1250 148871007 148871027
    0x40e0f070314150f040b1f0302100903080409061406030c03060904170c10150302012a0212061006110c010c03050f0d060e061f0e0a03021003051506130303 68
    0x104103032403a00750041540d8007411420307520804c200500c1d40800052200618007941c0120116a80f0308241c81481511b044203141804040e00c240c003070601ea441031a00807440ea400a56001c82c9180c0c5880e40d4180000c0242518030609030320324110507550b0040c3c944142200e103c1e180d84a00a8195111107007400b400c5400100b0803100c484104010281c0c542650000c0d08801d011403004101590101d50314009580c000c0b4801d140c442c2560800307000507a0809988420510396107100019a6826000c1c5c0d170b244101c409000c0e4200010b4102c00c3c0114201003141807040c1140600d02a94554400045580100040448030640c000c0740c160207040d07108403440f101d464028a01903080c6a09018082e641d80e000005007070710940e48480c1000441d0700c0108107948920111209080040380010300b40b031400c1a101d807001009441c6079004600c0c1c1c0c83c840c02001841e00600680032040c00c1c0300d8007a00800060301e0703490f842552300c64540468500b4104a4805083c10000302c41a1851994192112412 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 148873507 1250 148872257 148872293
    0x7050c010f0905060402040609110d091a010f0312090e010306090f02191a040608010b1b010609020304020924060702060f0d150e0103110906030a020d0809040e0f0703 73
    0x740c0c058816101124003502410038020b0014002d1418140b04004c00c0701c0380c9500c4010610f09092604c129040b00b070094030080b4440d40404506003486203082c80344056521400f000740034880c4004604119a00d07143c0c0184c80c03140007568041075007248295400e20142c03242c8984000504010310005031030b80c00c00c040303c0b40b00c3e4000ca808410294002180c16107408542d480714500d041c001c100700f042c0644180c180e1100003400e945400d0a041d0000c200701014040e10600040010b403205c13600214144036004201c800c80204213050312480b0f1200650b20035075050340320321451804601c810400c2c000c0030b0310500d01d4031509030024101c070090010b180c02c1040140d904c4031081c0f0514990340140c00090403140b83d0b18400184006c3e140f039400d0420140343d0801611070319240014070014058200038007098804441c140c1040d620701c400a4a8180c5c000d0b8020340202e0481a101c0030080b0b0303140540091942164140f05008107548403d90703035090028420541d500c101e400300007140c01d0041032081244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 148874757 1250 148873507 148873511
    0x3090d0c0f0f06051501051809130f0303020a08071107140103110c0606010f050c1005040f050102220b1c091b031412090123190806040e01020406050307050c01 70
    0x90582c981551032484103200360307502030b1144100406014080c030030407101c080c24240b00e810b010b002c46000c0c4664181c03000943c040d05401c40030541c00e2007842d1449038015844481d20102c5140d5283c020069004582444046035072500400c0a550107200761000701810000140415032030075a01da6508003c2d004800d060555070b00c03500d40341d40c40700e100414240072030100400c000d080c0203000400001c9201421810032405109405130602e02091085c404041b48001160b44d4449041c5504000700b0f01400514661001400340c1004401c0058034045a0221040b260010358074181d01c00315100e4690340400c0800700390808020001a030b440b8541040c010080030050464210030a00d40c0f00725900b06480c2071211a45424240b03c00300000466002c0100700b0506000340c003000a0500e883c181c0b044c1c4041c4006c1e10130302c0480d000ca10f05403910850b2500d00004411035000c405400b850b4107503403c2d4010303410400b407103140c1c800c1402220225600760b0341d43c0b407451351810800c80c0c051300540601e0030255 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 148876007 1250 148874757 148874783
    0x2100509060403030203091207030209180c041425050f03101e09060518010512010f150e0a0507020d080c0c031305041d19050106030b0c03041703090d0c 67
    0x14070741c0380180014500c641c000b5a41ea0400804010b074401491130220b03656071080c4400d00c0161680040e480d001320800030340000d0172914000c80780c1056001195290003034600284903841e005980f241d2401b4001c0700710b2001d9a1260010445000c076010381d00e400c081401008000a0003818000840c3d008841c02ca100e59080c1c0c40d1141c11064044c0c8101255164400f401d0a001180d40b902c5004020a02203c0701461621030328299030f03100d40144512132007001520034a413941542900206050b49440c02c0420483c0d0060380e180d07040800c1c0740581140c0e81b500400051104001d0720485028a4164000b84006458400100d880100c0140b1300414104203019440001c0302c204041c0200405004000068909100030700048800e03011045601d21440c1d940c8440e01d60001c1400800006900e446031003001c40c07401d240b07000d840e00703500092981c1e0254080000d0901044050750040340b0800a00c174014101c240c00001c0b900040e1410070b8035411415034001002d010764041400c0a00ca01c000d10100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 148877257 1250 148876007 148876009
    0x1021b0111100606020708031303030c02030a140706030b060723031b011e09021503270a03080603150105191e031b0b070f060b09040807021c080702100509 68
    0xc468040710b0190f0301c440050003429018000031014000020082d0704059030468114402c640511014061010050501d401d5440a01c0030500c540e03000300041c1540620300208640e200c0c190701c0f402001a107482224011441c01c982110324464200d5000d240c503908000d90015078072006401304d1406d100810000c1c42c1c01128566080c5680c0502000103950f44140040c60407101002c00703040042c13032600250200607a1140d058a0550384461450358595a841c010f144600705010003059001c0c00062159004071b030002411440c0c40d1290740c66010035114002410344d0303010884501005440e54000601c039078100103841010228441c500c081d4601d50360510034050740403209507030300c104503844400d1083c07042d104503a9060b0582c02e80c2c2090340c146071800c1170446000c1e0071401044420310000c40010b0000713a4009214204000344284a00d00342031030b06500035409004200d01035a0719904405100da00c3c0200c41d1000d03500840744503c4d0140560800c0302181c40001d00c82c1c01d106040c0043c4103a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 148878507 1250 148877257 148877263
    0x10207031202070e1006021b15070b09070501090819060b060d1506081e18030a0906080901090308040605130c0609050103060e01050319082203020f0d0201021b0111 72
    0x80c0768150040c10210307040807003261000f42c005200f80044454407004004940e0300040102d059600340115003081104440040d84020898a001c60324000114030780c001c1c8826443c107075001d44001c108860b80c3d00c4d070750801900d1403d9a80300e51813258100b10750b00c1460329010741201003003a1240030300140f811009000500d4a4100a1640801c95903684a00400d0540c881c02c8a01070314690030704070f442c4d00e0049008078640b56003061088011001002103006401da400741d0f09904140401605c1d1640c9030081c00526058182c418100002d001070080740e2060b0040c81104080d98060356000456552030321402e01608020b400700b0540f0300c3c803c030140085440b4a101030040c0c4845d6a50f408001d02d0140018180c0b12160130186000c1202c000401250341c000400384141004c1518484242c0018240f1490714094510505000b00300300a10340d804182c03046090043c0c034401c88800a030308149400340000b00e01103c100a015070304c00301700782c0e04621840891510b801c505241c08480d12802c4445c40f42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 148879757 1250 148878507 148878533
    0x40c0b0a2105011401110d0c03021011030601081003030504140f03060c0316090524070b0907050103111c0e03130b0d05090d0806010c060f021303021509010c1101020703 74
    0x4400c541d2100180840e15180c200200343c2602403800c051b101014504446e00c84064101840c04e05c54030082c20400c01d030091155101806a00e0020045034480ba1441c4150350300480340c050008a5010004646101140004095a8160307494904180c185500c40c80010700100c18150f20072170000105840b540c040004c1c3d840307600d0100300c990301e900b44484040c0d450010803168038280803c0711804d0001d40c0310485608070324a4046181c0a040c00f0300703d41c010f04c074450500c0c0170f441c00041c401003003100741001841070220341003a6001c00482e1017010040d0060701400550303061800c0d0703203504181c1d11f81c2150002030b40a20304000b1349103003030204150b40306032000702c8d401200174990120b000c4010000354402d0552105841c000340c03250414500c001012a0703070040074203040c00030421544040c480c07a54810101b000400004542d111920001d86250b001e09101c2244111032a0500c24441c00300d000c02d40d0340c2204180c4400c069812241c0c0c0300c895480030200c4260452003040400004244d24641645c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 148881007 1250 148879757 148879817
    0x50c030d06050405060f090615070f030305091501030b06090c0c070f291608041a0d0c020304050a0302041107060504030c060501150807050a1e030c0e030105040c0b0a 73
    0x59420b1030b1106110a4a00040a080c0b1400d4031000306e00e841c0d101c00401c5580680c0807504135402c11300001c102940c074018008040c0c2456419051101050740540c00740340600c0d2040700f16a04c0150442000350f26070000d00000300540b84d14804246c0300c4c1013646c01c4c40e07006445810718a041a00604820f45425041e0307210505d11580e1ba45e040040a1546202c00d131418001e80003088030107a000407183e1544070321000054040312151120b01031013602000e403405003106424400090101d000805060f400000f02d01c2c1d84c00e8945440340d0882400003080f03504440c00030b800010b01c01c0ca5034003000000c0c4454001003c40e4070741000200b0000e9201c0c030600e44920b119407074003102e110301410284110391f8140c002026550312015260403064000c800c00e0350000c0503150896641da2220301c1102c2c02c0b2100420346450041b40041c0c240c5207a0075410420381d4a205554240082901004150a9031402c0d1000b0f0300007245c0361700a01002e088640142000e00c20742c2440401050943c480b8260440c62424075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 148882257 1250 148881007 148881011
    0x708060c091203040501020319030f0c030507020c0117151201020a0305071202040506071403160302030a0216150c030207080304030629150a0e09040609030206090d140a050c030d 78
    0x418150b203002500008030848140045043c24240342c0042c0d502d211315942c5030303848224146c2c081c45041c0f0940050142c4021000c00344102d170884140603001d41802e41d045400750249000715400c03540f00304441150308001101c5181d07683c480c1c40058000a040c6040c5507000391982c41400000c042c240001e00c1c0c00200c9a0b800201840d212100803c0000d10700785d480745040c01000104103540d034110580d142d2540064604421031022450a40b440c031490710118800701d0395884542c01c0c150080090003164085400755051040014400c076104003950041162421030b242c241c5008034031801d1344000c024820b004440360b06859035101440e42d007180d80119a0303180c50700d12091880301032840410216103c2e01c10180d00442e031360002551075410b170507807070513420020483c0c0da5000c2c811110490344000142c13582c5041d0815080640140c4420b210980c054814140842d50180c0e00007003904034074040780d9410360860101607442d442e9500010b64501048428815080883d0090000b00001030800b040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 148883507 1250 148882257 148882267
    0x15071101021e030a050901090801140105040605040e070317090d050c010314090303040f0302010b0a0e10121a0402040b09090d020d020c0f060d061a07030201140403050d0504050708060c 81
    0xa1408044801c5903461003004080031442d03680003c2900d07101045410403a8444d040d66004848003d92039100002a600308082c030f05909017005142416168180e60034800d1079120024003040c1c0d6203202c61030865501400003007000c641d040290140d00f85280703484c1c924150541c2c00044100780c1d5060f007030340d0701d400c90413654466680610070080303a03031003084040c5013602c0c101801e50b4036400010030142c1032919100b81c61040601c01e5103d00e18290005104c0c901c0592560841c0152038400c842c0d205031032030503000208081a480e040010a5a409104e030000c0f20352000140c0c880d5140504101d030001e444825400311941e0780c0b070025206100020040c524140141f80003854074200b11180810b5400c041c450580e0342e1100ca2004089610650b2482d80d5103090a070078a0003043c50764468444040722039500b90285810b1002090307058025030092000b00600c2e04a00d407900c43c155001008514200600091003006400980e4807038050015100350543e29928241861800c5560b00e0ba00c0c1000a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 148884757 1250 148883507 148883509
    0x904060f060620010b0f01050c100c0216050a0e070c060b0d11130c083d0303090e0708010e040f1227050904060510210b070e030a020f150711 62
    0x3030f00e80e01c07190032802880b50311504008101c140e005005498108107001030450502c003020000840c4201081d002000702180c9000d00075202c1001c0d400b541005039403202c00060740c0c030b4107140400076242d0202502d03445403911141543d1420303281e40300306c030480d07200d407039003445070342e40ca5840501c442c05034115500f03c1084204200d50001d058107010f15513454038014195490f4000e1855902140f60a410040450352030b41d080c00032001e6403006001200300c0ad00100100d8980041c1e40116842a2940c180241c0c4403000303241e00410032140b40000500800040221460440f90250820b0042e5043e07840800252603903060641081d0503400400e840108442d0700e0400c1202e21500e80c102ca04168201c5401c15000440c1c1283c0a00701400882c0c840002c40c41001c482d0650800428901c4104890f0b504032407100d1507000200c20003a1240042c4100045086009680c40c0d81d04c3d020040c09000680019400c00071a01503100c0c18039017203414541c010240f0140840204540e0b40140b0341d6007902d00c0248 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 148886007 1250 148884757 148884797
    0x71b060f0306050d030e040c02030405030105040c0f0621110c0312090c0406030206030a09060612050a201305070302090a08070305070b0c03030a11130e06010e1e0904060f0606 77
    0x26100c075008420603000038000c203906c0000c0c103007032003001c4070081000609614121700d5030149401440d0f042d40b80600744000c00172011071f29022281c43c20180300300199140300c1669204c00b40c5c0d075441540d49089900000503015507103c0302e034a2444007609410b00b00c8016120345160800d001c098600c0b00600d0501840c11020406020a503038119030500070b00b821540480c140e40005401aa803041c0c85658880c01c000807074002170041c00e41039514103904006401d000d5074490080d801500c80f204502d40c82160391a1800d10016819006840300d01d010000420000c0200b00061001c010950309200c940d4483d0764100c02c80300107205440040c8102c90540c00c1c0f0605103a00341d4455212041d04214080c203890000c002e5170345c01045604001580340912020400f9481404c280e01d1940c8880c0303030040f50000016400c4c90107000280d0300c000c43c2440002c184656407061701d5880f9060110380228032050319010f00f1a50b03005108401c0411354851119440040c1c50954022002043e02d42548402c004a28 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 148887257 1250 148886007 148886009
    0x6190801051801200309120c0a0b06010e0a05120718090501050609040b010e0c120703051602150117070b0a02010b090c03011202041112010e060f0105040f0b071b060f0306 75
    0x2440200403000e030841004054080c01189540c2d869801700000e40c417000d0078040d20303075009030a0360ba16944400d00c0c2c540f55100c44510300c04840d40003072000030513a194842c201010b4103440107030855100d24104401c115200800a004c0021031003600000b003041800c040e00c06000048074000410243c100386449400d4920080c8003500810042d41004080340c0714492040c119182203001d43c2c950746598103100007034401c1504110440c41c4c46010300594030751590149204204030408441f68000000080b612860300500c40d880e0f000c035540040c001485510646440b10700716601315807009981c0c00765070300c59802c28000c080260b50b544e03070701c001c0307a05201d0180303a4080c9440e61100d1456042c02c03007074071031a100303810003034007981d602d841c400284601e0300221404186040701c042d9441d07039503800c0d16080e100100c41146c0562040b80d00d2414650289081d682680d1140107000a16801c00c0c40c05134058000b480192541b040140b100081111100c1440d03000e041a0760b6182104030703014002a00b91002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 148888507 1250 148887257 148887301
    0xc1b0705120f070521030f1806070533010b0d151802030c0702130507090801020f030f07021c03050907060f020c010e060922050a0603030f080619080105 67
    0x4002c124560400850520700391103084850894900c402d4070501c030f00540940000304c16100002d02400da40b1080740203400540c181007168403070703c0a5842030241c43d008020004005500c9180b0441000445c041d844820a49a440c414402c049e601d5101406020030b80c80b281680788001507981c01c6c80040e004000800310007103000f18a26141030100c01081081d8600e04916503404008500010801c40460340f4440d0000c1c01c010450040e83c0700f41e002000b06544040c04250446000a0708030f006000790361109451110007815503032540d0303088034801c1c8020803101c1180110510411082441282c074940552150307000100ba1414010321031138240c040d0070a0061108900082400c5a40000e141c115150207207449516003407108046000c500038880754941c000b8000310305802001880b0309480c1c1c014034610040c009922041d052008490039400094001007200e100c84102e00e01030a84d2035080381d4040c02042401064040c1a16541400d80110803165155418040c18564001d02d407110241 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 148889757 1250 148888507 148888513
    0x51c09061e0221100605030705360913110a05040203041208060303031003081b1207051005010308030402090903070501050406060305061b09120102070f050a03080a051b030c1b070512 80
    0x1080d801c0354401341203510924041150010000384510300c40d40564006000100d00e0496440c0c41c5141c075000366541c0d210003610021101c2801910b4030305043c070030f03001d0b44151005070718015130340d29844884802500703215005041e83c0000140d680380c500c02544680d00883c51030300c240154040083c040580501400d01c240d2003401440b00c280da0026601049941c0060702d650b45903600c203648a07a1030744804403140039005060311404020a0b490041c0741882c4108252101690281d021001b02c3d0b8080c0000340244905200050040c00c0c80c42c980c42d0040c801e80e003140d040ac1c50540c0e9140c2520780c103c13011920a07807603640810401008215070343e00880e8041244001403903804107580d1034003503291454481c200c4a6020740c0555820340c12904030540000e1100034940c441e040c605d51742c646c080030031400911410005040e001c01482400c3c0110743c1b90b07040101441d0721490b0300c0c60503000500f89890700681000191880c50100007048840c01484000c0c001113490501042038011251411481c150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 148891007 1250 148889757 148889761
    0x4060f1e031e020c0c0d02030c13050106021612060e120d02040302010e0108130b1008010203040804210302060106200f070801050901090302070b070f050d120c051c09061e0221 77
    0x82840f82021a0aa84640308441c4d00d000007441c00601421940d040407440e080c1e42b00582654100605890007030b02100c104542c211078100b0101810311440c6004840ca95101c0b00051983c0c1000c040a11500210341851080c015079048550001c04240c96a90340050104210350700402450b030f044c0c000b42800040c901d0b20058046242400d541c1c010881030030f10001032045855001c464020b4480300c00210746030b2419140000301503100340a941520011400f0b050308000703440114103021903042d409803001303900c0c000084d82c44032000b4030111607502c1c54444c0c6100030401040500c0b21551494010590145803c0d8202d0071a0805403890483c1d03410965440c010980001c0c1120440e10790301c83c0182d903006c0314108a280040c50000081070341c041c454100710074036030101d10030b8000e98004808000e8810310301e80554141c0f160303010000e003a11a40040380c2840406901c0010054001c05000c11801058034503081101e10924404001a0340803504111084091405481d0708200d08440c4500f8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 148892257 1250 148891007 148891027
    0x13080606010e061207020f0f010501170f1c0306120b1f0b0f0705030f0a0f020c0a1d0402010e0909031209010917030a06050a03080301080f070b04060f1e031e02 70
    0x203104c1d18448121802880002c40d145600c02c00ca20000349007d64141e0b50044204181c06000e82000e20071101c0301c482441d03410102d41000b18282c0c589141d060010700c021030780b6030b50080301d41c002c20305807c0c09d0503950040001d04660000842107032601c02c45440f00d0782e00d0070f80f01070441280481c8036a8280d2a8043d41408100c0214089940007100c402e1000d0700c59803c0e2828514603c903045461464a41c08110808541d400c00c0e03100304d488420342c0039141809071030700c240848400c00c3d10810130294030f0901654440c68030182c5e0035411900600d00b42702040049000701d0040351003656007461560000031003881503000701c40d4864020245400910202031a03850304005e011180b0901c050728035001010030a241d03e0303644480010000508180c05443c0d0303c2c20488200d4009111740f05040c00382418181c460400480c511041e102c0006080d420142813500c103c840c41e07002d0002d14240458104c0d9480602445c51803000c20860564000c60301019030386c040c03c4544d4249080c0140d00380188028921 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 148893507 1250 148892257 148892269
    0x3120405010509010501140607080d060b1b06040803010515070f03050915070210080c0403050a050607030c170c130e0c1917070309020d020603040302010902012c120309030313080606010e 82
    0x10440c003110a2909e6503c40e0504070070324401c0042030803810746005800a41e012002014200b50089400021001c0346600000c946881c4100d170014143c1c4001c10041c000c914010300340c00c4060915074019410010155520780000d40c02c0441039000c01d5001c240d591403490207112081c8446000900c00d41404c010780d001c50b4582011090940c20700030300400207909011440261001182c01104443d8002d00e2400d0040c0c0710102522701c43c00080c20011980c800c1d90187d44240090904896900f6069461ba128503803541c02541581f1429400341c0000038681c401055083d01920130305842542c0d41400f03040059001c100e2031908004e014540460868401402c4142684444907050114000300c1350b00c0011201c00712148001d500c071f02c003c0280810715905600086896100b80ca03188031000e15003c076002c4820b210180c031a07449600c1446801c00d824465a40e542c01c40364401100d003000c0c05040020b0458200e450b514803648040002046440810001a0341159084c200f10350f010f50034a0101e40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 148894757 1250 148893507 148893539
    0xf051005070c05150718090509010b0a15031a0d0b16140415051b1b030115030204020c0c0d03080f07030204230a08010c210c05250503120405010509010501 68
    0x8007a9180c000000e00c3c843c01000148501e01e00f0715a8503080c2515810200d0023400160354001e402c0d8603005900f145410071090080540b4408409c0c400c401c50401c07411400307001c0c6569454039806200042805940f502030402c240b0720b2203442e50503254584140480300307481050410b0b00420016480d0700e1030a4a440080301c01b560140d40c400d8150162240e0159103034814212401e01d500c1c000540c1c2c140c600b8000c52111031050301d2480401030321420cc410175098903e01240310f02d20104c0e1711020001480d09900030007510414405481070403009800144200711540401c2e004580d0350360802c00d1580d2902c0d51107038800c185007001c604082c24951203007a103010062036100350b0318044440e00c03e0340d034070020224020b042d908024003103080042d4004041081da500581020700b02d1036400412443d0a00644400c500e13290b503290300f0b1542e11000e4070070070350038074180782c004c0a07250008001081c001d0000301440c0361181c0c405066800c007840d01ca0f0031514010520a8164904001880780c50f650b100040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 148896007 1250 148894757 148894783
    0x60b043215090705070c031202011a1507060b09010608090f01091211031201090605040f050c0708130801020708071202060402011e05130906050312070f0209040f0f051005070c05 78
    0x100e09543d0010150b5141c450a103001e08100e60038800042040316801d040b15403111168000e0045401c600400f08102d004800307041d038880c10101c0c0170303140d1030181000380042600900c0045004040e03500032910b41c4100381c0008002900351000c20003c084104007205c0050f00c1d0300020000410261100c50100541641450030425048a14581e1a404106850f900408030018581c070f07503510407042c0000c100c10f104440c0903604001c0200410700503072060512502c105120245031410a07035a066082c0e0088080c00002d00e06920040b0314800d003480948841441091026950503950514150740b1040044180031540322408000050340e100000c1c10b1a140100c80c00300d003900951030284c8050148031032112404c030071180c00151030b0046400020440700142c05030766514040702c0c0164078074424020007030301c0c4a403a12401e80043c140b05680341d60140c021070036800b0b1081c103a9911480040034280c2594240d0210040701d641d460184501c60708a003140c102104c0300100ca0ba116030303c0d1225a2406 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 148897257 1250 148896007 148896019
    0x15030907061d04020309010912111504021c0602090f0a050102190606080a03050904060e0714070201021203041109010e010614070203281505010308070f060b043215 72
    0xb0100d09681002d000140180150740b03a2910b040f62500800681e80709031222050b141d4004c0c44035005040911a0b141e070300c005030038420318100100c03002c01c802800880e0000b00e03031108005050003a01c14015181e104500240e038868001c010058240d503c2c004403486510904001c0203c0ea0300020440480c2010701d21100c044c0722141005002801107034010082402495041010140d000c4028960908120350030402d094481c05030402405040390030901084811441001000541002d4016944140704580205161522200132500141d8080312135015030b812a1405240c028049800b401c0c1c2d403440c0844030f41c0741c4040184180c0c1017480230003203040000741940964034140103131000c135400070380d41c41403520244171006911400020b0945003c03078024103000ca00382c0d5901034a41201d40114080d030411950381c0b41d1000800124008541c040c0d5940260b51043c0c0b2640180840454105486110280d4184a1150402242800307142c020300210400141103000409119100001c0c0d0301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 148898507 1250 148897257 148897277
    0x50f010f030b150c0114070c031b12080108150f0105040e0109141c02010b09040b07020f010c0e012604141524060310030303020903010b040e0c1503090706 68
    0x40e4010300344101c4035500140150f20040114200500803d0744d01a43c82c001c104201598041000089080c2e0700680051900810003011a01c0b034031501d42800407682c10814824201e60b618803c81506003840c0c4080b41c0c040d80104640e08050200d948908080b12114180f0b00d4240e607030100b05901401103d00c581e5072031a0449002c1005d600400c0ca0541c0000d954040c6802c030411165110040b000103e42a05843c03001300304d00f48107000344140c919015141038100d864079a16031507459001000cac0000c500c210342d000c080c802d03400d000719200c0d604541c88020b18001810001041c29801844440e40d04c00492002580903580c41e600310f50040d00501e0200e812110360300100e050000032584c1554030402c01003444031010300c010380e400030580c4642c40c2c900001e41d0b52061042c035000071120349503284107d03002080860301a40082101d04070040001945440b65800201102d040011b81d84542c1d02c4480d144596045c20400503d4900c041b62070305065140200c081c1c1e5941035035024240401c05005c070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 148899757 1250 148898507 148898537
    0xc250503150703110903010e0304090b030a120c030302070209040f030201200f0a09031203060e07030e0a060e011b030e010c0201090c1a0d020301150207230f12010501060206070e0406050f01 83
    0x45d00c98540000340240445404084065581c1d005030180728541d519090005c1003520b070004028080b140d018001840c100804a010381310352240903002e03428940c0800108006980709002d251003140f080d070b901c0f1019103003820003d08403404c00c042403201d00c41d408a810455020041a1840422840340a0743e8940c6070804c201c600c0e0129600c01400b444501d25015034032138054000b6002d540200103401c6856650342400c4064880030082a0311540180c8004000304900e07801c802100e100d0b000020445004a203c0140003a07a2010148002542c400f04406011020300907003140303d030544001c0c45080210b842d4800710805a2207110704c43c404101103d0131140c1c07100151517817030144203003c64496a441420300084c241441440f4018050b885000c1030030700c000c0441c0d14214168900c000c1007811543e0600c8007480c1c900c0d04082d07006800e0075021909040c2400707100d0180c41183d014200b0303410001405001c000d03000c4440c612550405030140001e8560401c9842035030030034a0005c41e40e0a02e11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 148901007 1250 148899757 148899791
    0xc060d090c080f010c0302120612010605120c01080105030c0108060603070e10050a020d1409040e030909090a0209090f100507180902040618080309040905030c250503150703 76
    0x1008025165640740090040c20215816959081007002840406520a8100d04a10a41960022140c414000b044003800d0500c0c1c00c107080c40c007a40c000140b50b07441d500041c4100480508000c29540440b40c1880d59590002e00c040c010107094008010540c1c82c0000030784405002000c1502600e408000030b5442445584a040c069201a068000801914000070910b61021380030201510480080120591240401c2009412040c0c886401e000b4181d041002034505c80442c9011840144200c40080d41c0b421051401010321400071b00d404207091041c0800b882c00140b000c68207800001c904d90600d400400c824586e41c009140c005480e40e40c0701c0c0c0540d00b80c0380a5003460071040d101c203004136002005600410554205440e800b18010203044502452009c601400d4210740007481006450304040d000b01107500d11400c16a8107007400341c5003903440c01c0d5600b418402003090340084520607000452110020b441e05a01505075014034200d100443c640c058804001c140d0380340801c0140036410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 148902257 1250 148901007 148901021
    0x80a030f17040c03020117070806041e0f05010515030403080411010c0506040c060e030102090307090b0f0916140a0203090111031e0912010e0d0c150c081b0405030c060d 74
    0x40030182156041c1403c144401051038007080740468200c1d407141ca42c04140b01f88440c4078440035503c0ba042c83c0e0720710f4280400303050703940058444aa810f80c55040c02200500840300c0d084a00d040024031580750400f001519000c1d000b90003100c0800704240400b180e4440038256111307130001c83c8844502c0c8007000403605030401c0c002c00b4200b80500d000380402c115070010460215034407562096440c42e11401098202d109070030000e5850340c40107600b04085200c540040d10300010042140180071070340e401180002070120b0f45007040900da00801611240c0141401103641c80003480681449d0f05039030040d589100340721180f414450742601c9010207460400490301e90f11a000c03071003000c9140e00c0391651a16004050038a204002503200b202011205210703940356080d50100511a05500c804190b0768190304403010b8402c143c0084030700650144500420a0240060790f03051030300d2801404609151002e2070340a5030f888010403041000da6000100800d01e0501118038070346c0e91510110300e100078605 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 148903507 1250 148902257 148902287
    0x2070c0603060e22151b030c1b060e01020c0a05010509011820040f090302011a01092d03140d0c12030b01030e0601030b010305120a2f06090c150301080a030f 69
    0x105054503014103106d030011000008006003028071120140d400f80c0641e45514408000035a501ca40c0110107074001a81c1030809002e20000254101002056800c0e130740002198006c1f07601c0082d4140410400b4840c0c00da0017501400200510f103c03040352034a240c105041d0182c8460b46c0c40601d0407a04010109028004200520400002880e034902c403014040920080d0301551030000c2c0100b1060b41c802e0040d0441d407051b51601d10040c100044030036055681c2508a100c42c0480d8010441c00e1000c1141e0400f03580501445400c43d117803101d04030316100e040d0382d1102c2000590403603a40020b42080880701003a00ba41804941000c00c600103c0003000d203180754002d135120303410001040c40002d095842c181c0c0d001383c0c240d079260451021a8600d61203000304020000c0c0c08041c82081d0201c42c01c0c061001c90805910041a040704010000d28110003602c283c8070ba50031004102c82145000b0144c0440c3c20700e1307014240c0c20341d858030390056100c3c551010b014050029403e0402002c0c0d110b00c4e449014007038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 148904757 1250 148903507 148903523
    0x200606010c060b03010c1115010e0a05091204030803010f090902010c031b02060415030608160918020d030815010201060302010e0d080c03030f06011b11120102040b04080102070c0603060e22 83
    0x6c088070006d144003081c045841180c060540107020485410350128140d5180c60070080c803e84440400000800d0028860a03050003100170707001861103904002d20046000e0f44429449504180b4411032044240e40401c141524007c40d0600607600118210003040e0581042c1c0911180300701440100c0a04541c029031001d030000d80440d00b1642404c1c00c0008844c01e030340410104d0307105c02c209a502c8282900c100b00c05610030360304200d081501d41001418401490001120b03505c0ba82c041885400440c60072008900039008000104091840000c0301c944240300078800a0300d1600080d10420080b0384880c041c402c100c0010040c441c801c021a01010381c1c06040340da070b91800351011180c80d001551020b0005040582d100103400304090140c4035103030401c0c002072192820001b004841428815002c90b155000d0000040b101d0700030019100401c0180000341e40d07100725107001c9800d01000e42001c000d05141000c20321560703c40d03044055108200d182d03140030189210b12002d440b44d03e0f1641c0240106 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 148906007 1250 148904757 148904771
    0x10303171017100b06091e04020706110702180613020c071703031005040603080901110c0907030c171006081504020409061e0b0a1809060b0a200606010c060b0301 71
    0x40e038000b841035500c50414101308001843c000400803284078010400d41e002c1e0840700d10b8005030074007031401c03450414010001441c103401c90303498034113071810781011440420011039140150b0611101c06020004440400c08262401100140781086440c51013003a0310341c0440c04c0b0403001e40030402803010b48428448505001220501d25580794411982d00c3c0459089890000e00d03801c05d4020002965800a20300d4140020440116510380c41c3c6414074038603114003045540503403103010040d40110182d59001c94054501e440140c070300380702a403881c16070b120a5800c100301400480c0060080e2a89442e06a486480f01101c20140e50142d00d0860f52052000078002004600c96220808542c0380403070201d18442d8010042d0b40180c410301c41d29032011020030949041d03a00c90361911100030007402845460315160390001c03080f41c0d001d4020101500000510b458095040312500403060580c0c1e03081490034121095407601c42c5809071107541031240c1c40d6640020442140c101c0300e641400580200158 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 148907257 1250 148906007 148906049
    0x1608190f0503030f04150507090b0a022d2b08040c030803090102030708060612010501050a180305010e010b031c05130e070815010f02120c031e090307050103050103031710 75
    0x1000d6501b142c910116030302003883d040607809070500c61840c54440c0e00071103240c2000001d0550281084808500548180c10f0001c1c00c0250314a029212002e41c92180171010101c4c10b1a140c61490304040004600902030040b000c0100001c0401c00309143c65129925a4a44000d6241040d00020030010000c820040c00c40c005502444c0310301000c1e1341c0e4086035100d83e018407440f44610300901c0b02c0402160b006020700d5000d14001c14030074145150140c12481c5604490b2030945441d007049505035126107841c0402803003400f402500000440207400c1a0804642107001d40c2083d003040003c0c4034000c41d07800c3c2199051203e6900801400350511160325101c200101007540441c1c503517100c00441c1d0b68029155200e40c540e21a003c51680091034101000b80b000c44140c0c0040704598007511042021501105145145150411113400d400d51940c80070401c040c2090310980200d41054540b40c01000429030210b00c90110f05040501c0d8602c0b521902c0101e0600b917003540042e040d08582e21100c1c111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 148908507 1250 148907257 148907281
    0x4020705061f15081503030d18060c0305102d151106010b0906031302031c0305090316120903060608030405010306092a022401081608190f050303 64
    0x11000d00352008540d94035051140f600421014001001484000c0002c4480c8454182c281d81720b2002422641021000c41852007580c5010040c0320104449100f4442001064000d070b040c0c030051820184401c0c40d2070100001c0b802d186118044c941091310340a4a01580c80d0350700d0400c5460400d0180b8101500c5452840d80355075050310640c0060100d928928240c080818034506a9250304030041c50520920100480c5400c090154860310304949900001a502044018480a02c8404100000590402c06400c40310010507503101038101700424001c1c0c0e49410646a10f16a10100b01680700c100740104271540c981c2504014500c03031520001056241000028208880007680c0503c101e5407503003071044c19248409000000d40700118a82d00c56060031011820440401c3c1c41282e028465003110440d040c898141c0740009036419000500c00780304140100841c120384031404004551603d205c2c0c5c0d50380c9090a16000030079500929000030840c01d002c1c0440e00da41c0000849032242401541d08403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 148909757 1250 148908507 148908541
    0x4030b0a090203060a15090902010512180601120f02010f1106010303030f0e0a0b07050913022b14070e0307090f0e0d1e03020d0b090a0b0a0b13050402090402070506 72
    0x2103c1d12612000030196405806904a80c2440b1500d4075030503490418400c026007044c402c102d06100781841003a403a5070030420014030882440e054088103105000e001400c102e0b060304400c206920b103403c20030205a4841e1403000480c2d0a103040c1803d500e11800480b9100241400d0403864061080004103155040d040783c070b00c51103021410003110001201e10740d62001c43c1e0000800381100c45000406070741c01940580350740c2202400c1c0c81818100e0b07400740c4c0101c0c1e01c0b00b950030380d0403031f418459280d241800c065a03506040f1102d0080000314040240800303444001445002040700380a40c410071914180038032001018407420070310440100543d008003030007055408165610034407109019141c80303007190a100080000c00410700910611049020307500c00f251064a660311091243c0180d142e04000c0751044114050000700000c01c0c0041010740f58295008420020040c0130b40100321980c0c0740940d04031070084500581d9082c4010105029010300c02c00074055004103000c0100136070490302e4083d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 148911007 1250 148909757 148909759
    0x303020606010c050a120c02060c0106060e01090e060d0c05040c0c110907081503010b12030a1202030c040b0c0f0703030c0512030f040813030210020f010506100f080c04030b0a0902 79
    0x504680d101401114a041000c0c00079080da84480341350b1010860386603140c1c035803009034509087d4014041e004502954819440219160b541e50020060316602c11081c5002c44001d20f0803418007880c20301c4100030101c002e8125446030309001501d00c01c201c8100c0c03140c001007802410600c860400080041c01240c2c90790810b4401c16045000c0d0b111500e05480194400c0b090740e114904c00740c80d00e0075054187c1c03110074a42c1d40c0540d40d80f01800541d43d110b6460140c40c0c801c0b0750046a40744500c00000340307180c001703800002e8510300500600241000385805d440640300425507050300d50300c80008071031810391000648092401083c0022042c141c0c407062a50010b4041c00c11140020003c02d0155200c0c4411078414610b00c040e00045000110280000c1440603500003403040841d840c2d800141807001041c8003940568002e06000b540c0c00000c0c050658010801c03125130843e1120b2000c09000b0368404c40c05d00e0208101900011681c0181c0c0d03080da000345410011050322458103080f480018000100c0030303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 148912257 1250 148911007 148911013
    0x9060905010504020f070b0703090b010e070e04050124020312090c030d091a07050f070605130602011103060907090f140a080115180b04020705010501050a0f08031213140601030302 79
    0x100b00c90070107008488103903610500f628036100f001d07101c0c10524803020b0102020940c4542c014000305d80000c03c024044c10201c002d09155040080c0044d000440402ca03041c021810304004018030405c1c1d44241c0000307144840051420321010000300c1c110b1040110a1b0384101c1414180445e21500103001d0482c1c0205400303c50071503040080640b46009036104809940812204190408414401030b00c00b85200d4400c07101c182070440c040e5414400c05130090000a0800310f003420a010001900030000c22550008008100812a8031340942c0700003004e0a020f010310501007038919101e842003000421a8105107030085444000d00c0360782c814040c60061140e00c90000108120806201c0c020f40c0083d8046002c181c035241c107400c0000c0045040042c0009075030307a804c1080310f4645000402903107104000003e101e6041404211980427940c0004042004490b4107109a1000000302d071503041090100000f19502e07146240c0303201c960031b1001020000105081c03031a0000002e100c074140d80c801d40039 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 148913507 1250 148912257 148912259
    0x306010b2a0606031e0712030509041b0801050d051c0e09010605030106030501140306070309031125120206030a0209030109020d050307050d02031602040902210a17070c210209010906090501 83
    0x5d05e00309141200d20700c003198000950401103400001c2c2d0201d0700038030900f462420130007498000b07802c441c2050001d6015290351181ea81c0080d5100303500c5809400200c0304c0515152407506c40550faa802070b1010104001c000100441e02801843ca408041400801021a640c2c40313220091694100780b10f03e10100c2d00b000004108a80c000c030800762044409002049541d9038400101c018188600e01a01482420180c1448150b010302885da036600c40c074040b00c144040365801c001d000100c40d51000da10684001400001130341e8050480b50800d80d00c6101580f1031b0008000280100414800294802000340c01441001004400742048034051420f07603003101d224000076a2644114118074201440900040700180740035030003880001e001030400113060071104000e1900c07219042900d80c595201074a0342080204c030f000c58840883d21000c40074106200c6903102c503210704443c010301001c01d0800b810f1140b020b00100044501039002041d0780c05a5941c0d0903902c0041c2890300903101d54504000c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 148914757 1250 148913507 148913533
    0x6030c0911070308061c06020301060c0c090c0503060d05100230040b13050709050106090806010b070c05090a2901030605030a0209010303030507020f030a09061d0306010b2a060603 79
    0x420b9584040e05522501501d90314030003000201e00710050305101320715500140c0804203041d480518041d141d141c48200e0039941e24145240700c19001d81c051500c0c1030a009009400c03131b83c03100549812001c02c1d200715103100850314010382803624020490220901c0490000001b20044500c80c501051500c02003556249000b014900140202c9018108113035003400301d90700c40360408003003149030701600c140c4a02d980c60300e80600c01c3d00d4003a88000001f40301994103002040c418043c0600421016036024600000c40c0d850304050a1680700c0c0d44d1162402c800010014240c50f00801c0809100c1e115a480c0e1101b80d56121070400001d4403941d0001c0d29011000c1018180001c803000b6242e0010701c0700701d4607840c590b800c034060b1800824401c11401159044d03071000300304002900700c00100d5110114130500b4041c000f01016410300c015608407a0707001701c180ca141c40124185064aa04503c007a68619a02044200c009910f402064500f00181100d910f0454045030f0103018034021800d841007422004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 148916007 1250 148914757 148914791
    0x30e03030f04020108090115080a122c010504030803131b0303080a090507050d0501061404020a0519020c06040305060f0c19111005010330020705090a0207020406030c09 74
    0x403080001c0c00c003000c0100d800356008501490348006400c00102d08292443c1780015209142d50100000740d118035894010000d140c3e086000070081d80c980100038540300d00008102c8040a80714910340301214031000780d180d1182c000c460107541c1264209590382010240d450008070140000d849103440800729107151380b2400c1d00b1104481c3c150340e84c1d100e6034031044a08801040040707012160341c03046003000138403a1108414030039031074002d0000140141c41c107401030801d01408440e440c41284100040c526007030b00b00e02a200c000c1b440c000a030f0509032400000303914150b91117282640c0320a010500004200c000906107124180d40c6400301c80c103403200344803000d29000700b140c52035050001d000107544036442025662183c8031035004907803004407040c010404440082e04113862001d050012000c00c80031241c4a41c0721000603103008000c0c0071a2080003074a902003030044910955428000c00e001e00441e40584011980046c02004065a249040e0240b0a010b101d42d54401d410300d01180035440080f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 148917257 1250 148916007 148916011
    0xd0f020f1c0204270f090201080106030903020106091107022d2205070507060c1e0f050c070602160f0e040206160c0303020c0a0e090309040504150507050a030e0303 72
    0x140a500d424100390107000e0168150488000030056800e02c00001c5419500340d13650455100300d0a0300780d02031429446401541c51003180150070b282401851001030b6440813609046034030170700e00061b440805160803070140c0300ea58030001c3c52a040580f0f0046083d114001070004038401c40c2e003132001064820346410310a40c0315241c40b201c000700210b64500703800d00c0d040b51411010441c2d5035031901c5418400010071210180d920b0400640c0104400c0304001003403103641030b86120f9081000d01500b2027017031813080b03140700001182045003081d562140341e8061003c1c2d8808070050703010f43c2c03100c64517107030020750318031300008041c8402c0085640013865244144501c0103594290715100d2080e0740700e0702800000c3c0c1c0300b500c1d100384211800c820480801c0c8000018009944664013030b080c07014600b01000074021071500601b4102500000740414403400100305c0302007110942d80400c041c2d45908241c43c078940f80d040c50f2090182454100b010303256022004000f094490340702000501e06d508546580d074001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 148918507 1250 148917257 148917277
    0x90a06081302040b011b0602040f1409180a08071b0b0a120209010e04090c140609011b0f020a0f090501170d081005060c07050f040b030a0f0512030702030d0f02 70
    0x50703941190054201600401101c10040c10300700c80240c140b510180d41080d0710380066880640c04202440f540039840c000741c0c014a0004d91001c0d80d884150001508036001a00a03024102a142920b00510091100203c4150004099612003000d42043d11280401c1c0007140103637001c0075004a105092038042d039801e00403d590304607008070003080030030096200c0c03804603044c026070500c6044a0f6945009901c5143c0c070035603030f20899a00c1c11010400048205102c45d1180c00c080c44100000e076441401401c0502d191007402042e882c02e0b060101c5051120035029401020b8004003240b0042900c56460071114030342400c01c0541c2e40c96131b21184854051000a4494211064050000f88140343d40c6411190840c40070400507960300c0000c400b0350240032607801da5082104100100c0c58003400d41900840c099406204044045000a44030503281c24010700740e0403004001d000303000b41041103004124a0030b10103644d0342094000603540383c0001003801c00320f5060940950000209000b66404020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 148919757 1250 148918507 148918531
    0x911032b030608030406111e1c02010501180f0b040212070801080312190f0e0708071403070509150a060c0209130305090d031202040b0a0912020a0303050307021011090a0608 76
    0x100b480c000b100c00317501e0540e0415452040031000218404404d001d404100b451f0801007070290042c10650109d000e006140700296490000100b000552034071111585c0082840009116800c01552f40001c0600800081c0c20a102240781480c0c12001d60929000707540c075484030310741a17a0f0742200e0b541d41d01ca803800c10880e0540c0000440ca08042540c0c84885042c25640d011641800305000001150191018040c2c194004101044500300601c459805000c402c0301c0c20071041140d8000c07036610340d5680f007524024454280080c100c0c450f030b511100c1000c40005c0501150310355541d0700170401c544006042c0d01c41e44856022510030b8280482c036410340d1760f241c1c69042c1800199810801944120002a024829501806058910315100030b00142003907030350694480b000e0b200b00030300342401c41e00300c0c1041d504223621604c05a42e43e0614035080b0f950501d4119035070350f94460124205181580e06400c0e103420200401c04868041d000741100e170b03105031560148160342c2c0e1403c0b1409881940e040c12500303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 148920863 1106 148919757 148919759
    0x3090c140d06090311122208070b0f040e010e06010906320708070606060e0303040f030b060a080d03092001091802070818010e060702130911032b0306080304 69
    0x3541154407e003e503041500459a410f41030280d8070707240c0304c081810407001d071214084401074902c0c1003030861607580d107880491008000f50360080c0821070860021401310b200e9191495a003010041c40b0180041612589141868104550105e541c0401c00c0c80045101d00c03000f0140944070301400980719242a0000382120410310300302e4443c1e001040b08001800e0700540f5807040e070360401c2e0300c8a4180c0340d030700c0007845009030380d801a512030240c500840d8806815900600d02940244615610040303003c2c030600f4410300070380c2c10710701280c08401c050110044903601c00984c1c1103071560061074030f101601e4142d2190000380e05480001e41050b995412541e120303142218007a403d444d020300345000c0740d00080300407165500405210740c3e40c2c640c070810b0007020542d8891501000d8251510052402424000300300c1d5051a09090400202c0e010b80e00c5200384582002c80320b403e03000d94102 = true := by decide +kernel

theorem cover : BRFrame.Cov 148741007 148920863 := by
  have h0 := BRFrame.cov_init 148741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 148741007 ≤ n) (h2 : n < 148920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
