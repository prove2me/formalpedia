-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:41:14.090106+00:00
-- url     : https://prove2.me/submissions/e5d3cd24-b822-433f-b805-f86977ed1776

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 744964028 ≤ n < 745143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 744965278 1250 744964028 744964037
    0xa09050d030c020102070204020d061a0c030405060f071b03050609071206090602270414010b03060d03021f020d0507051e0c151303020615010215220308010f090606 72
    0x101003420841c0240041400242103541c2404007038016a0f0301c2c0018001083c4490000c201203042150402410015040000300007100b000308100729031003c400d407030481c0c00c1100c6050701c818151804c1c0100340308659004208550741c4140d00c0d07065944414510a480c00354044403481d0307444c3c0c4a01555501a0302847c8407240e40303002c1400004080380c0021583c20300c0b4100150624a03409072010400d801e04030746100c81110251041014101442883d2390803242045c1c03c0b01c03d51408070940341030312015240b00e000709005804d07a010b240c020844404120007030017003042d201c01c4407000c07000290002e85050303040da800c000c041506107124906481151180003820400024107014003d059031015054103080e01825030502c403020f8010f54030314842d140c09100c081d22281a45002070401c1c500408101d800f800040c0c402c600350740d0025140540580c1c8041815054644d407a09001c0c1701d0303403000d450000c0705041c0420402c050b0b000d038104e41254416214100b141c0d840701404000d5659074042c1c140042d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 744966528 1250 744965278 744965293
    0x3071d03071707090501060915020105010b040311040b03032b060501050405130b0306070f03450b1e07090b0304081c0f150501051801260411090a0905 66
    0x15084180342d21071140e203402c03682d200c0d84d504c0c20700b020f403003003603008a0100e81501d00401070300412408041202e034062000b00965030500c00b4032469400340e400301801d5405502114011a15203510130800301c9401000c5a0b150802c0c0b8100d81d4018003213107045240c0d00000841400005014040c240c03d40d80143c65040c2010306003018007408074804640d4050854407071b407403800c190b1402c1c00741e507000b44181d44c0d03983c4007416107140103420703900e0241040200c400f2280c0d00d0400554070003030310003504904000c0d40e41c104420040300300ba091004180980090900c200740000b55401110307101d130004201001021980e03503202c0c01c0e030710600c80381319015200703104000140001e450b45005001031661051071803c2c0b00349140b0f00c14116002402130340c1c0356566902010004850300040003006210900e012894000e158080e6400900403030081c50501c1203010340c030140b841e500444000d202a5241441c4100d140600f4502d0104107207c0216000705800c101003035216202d8051444525003000c010720b91b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 744967778 1250 744966528 744966539
    0x3040b011226030103060e03030601200c0301050f06040c17162105011806030206091c080f0d060b0a200304050307080c03012703032a0503071d0307 65
    0xa000d9600002c4482d0090808040c441103808002032031000001c040103926581985891011a19983ca5254030b903032003030041010513a440031114281d060b413001041c0400c408000d920385083c0f02c1c58049a85542000c0800400101101d04a485803c007140c00b8400348a240300241c4003030005002d15550014080c0c000380160812806000c6189070724502000c082d03900348442510040218910001d0326101d230b004203c050000c1c910322126511826040004510316030000d00680303d0044501c0c054565900e003400711405a410b4440c8054120104c0323681c8520001c294081a8021088411424a84003010a403090740005071117a80a290316601e0329410030705a4a0b4024401081d04055448100300208850702c0a0002c0d9004041840041441c480c2010402d07007506d101088100011120354081d025900040c5007808040340c142c100003400c42c2841c1c6c120352001e203099600c0c40e642428419005141303a486801980f240600743e03241c01e001c07090303a54848115440c0341080e03a803560000000b40207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 744969028 1250 744967778 744967799
    0x1050c07122a090e16060c050105010e0702031c0e010501180c03050f130c08100608070e070504150309170408010c030e0c04020912010c030b15031012081c2003040b01 73
    0x108801c050803034041c0034418005d0442c800c0b094000b1800075520034001020000b090040c0d40c00b400740005060124075280c0002940d90040160004003402d42950030050304140c0c2c0c0c44944100c81001c0240525a10354403c076000e00c0c025580740c414145004181c80c0361a100307100e420300401941c0d02c1c0e201c0646668180b84400c010300b86040e607910440030f80000e0b4480c01006039484081c0c1c01007011940d41d185c201c1036801c0000707940c03010300044540420413040f40d41c804200c2d0191081100030041404507140110000c01e540200140350620881403031440c1d140d058003a008690116000f800f413a40c81403001c0742070700ca0000325802c49910207010403000b460241c000e003040071405007105040c4401d130f24210303080d40d41100c00a070110b55600703840c0046042c0390b10740d428404036041002c0d15500345902c2e1484010b200340b142c1c1e1026400044900c1c10810084215203054001040040b0003060b0660042c008180d0001c00303058a05075003180042034209203060324415600012424110fa00c0d007500d0a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 744970278 1250 744969028 744969041
    0x20c101202090a03060614030c090f092514030109050706140f0409060e060909060402041802061306081305060402060a180e0402130e1b01050c07122a09 67
    0x255030a4090203850b000703807100d5a5540040d405010041040b5251813000a8010700d0f004e251030280d00008a07030308494845841c0640c10800521000400313540e8040d40c54200980c0040c40788038154800030340c02c035803030890b0700400030750f030b03000300e161030101c62041c101402c031030400800a01641048104004550140321780f03660210076070544030f1808051020a140b1980141c2001c00c0280d42c1d02c40506c01c0e000780c1d80403664402c00c2a0b80031405070a04402c49941c450f4000c000a2003552602000da102c1c541e099800c03e840c0d54040c113116121044000c0e01c0d03040301451b02a403c0013a400e880014045005224003803c40d41e000703c0030300380c40d440315001d10480d60300c01080f0341d0503c04000c0700c83c8044940b170800f40d00140040320020702541050320402c8a079204c01c0f0400650b03d41428030326407030403002290401c018a00341d00c0000601c801400140c40c13034010350041400c07900488200280081d4104440020180305542c104a990001c1d45501000399120401c0307100281d18040600140d41c065000c070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 744971528 1250 744970278 744970307
    0x1240302040f031407090c0504030b040c030807030f082d090705190e071d06030a1d0c01180e010b1309060b09090f010b0d0b0d02030d02030a0f020c10 66
    0x50310302078403050804918012503104940700c113040440281030380400c0c0b001c8000b8210400050202e5400400000c00500603808007610095000c0003090030014801d80120007981d00031861504da825600f005007414207900c1018012501b05400500050321214840d103401450040f4480484029000100c000000600c1003000348913500020409a40c0d100d8840341282480703804a814500705012850f00c1c0e03001400074424401e602c1c1c0d02c0011407503a82003200300c406080d91a5030f02c90307490040700b0002d003007007204007101c02402403056541d900c000705015900c0042030300d800c02016900110f0745014007643c0f1070b00180d40d03208001071010a0004004005010f440100d180742c0c01d4030388404108451083c1e028066140c400104044982080381c1000d502446c4140000c0d04c035032402000c0c0300070b4822450b201c0d0115035903004194540c0d50f00e610070081650054115144140003010103962030303001c20801e41c0821020044114118400a50000b100401810001e10403507010410b80d200700480c00ac0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 744972778 1250 744971528 744971531
    0x1526071b030311030a09150b0307062f06060102010b060c06070c0c0305011401090f0207020a1e03231507090608070c120f091406070f050c0d080706050a05012403 71
    0x81540700c0f403010146014045c01e0700300080f0403425141c5008500c021001d4914403d0410a000c80705640101d802c608560040c01c201080c030500c0880040c0c2901c0c00402880031903a003030500d110540000840d94420013082e00200032541c0107400300300960017107080c0000581e11000c0020804c0d44141e400e5103001c0d10500407400402c1d240d60f134a82c00e403584030a01d01d814017a8000100080c1005d40100c40c90080c1d0608218036000c0c2a4010410020480c040c02d900c038130301c1d00c000c0c545d40340041c00c4440007150000c41c42d410210360102031003010f01b0013018004852289003117984030202011252070144400c0d8076188c0d0924a0000d041d01c0e0480c00030190018411003030b0a500c0171030000703c2280c510080303a958412101d5680c0390041e1178400e25030003c0003d1069096080210345820040b07905098103c0d8041056903030350300e0441d160000840019801038680032580c0101b004520181848500c548418007150f56442610021518248070381c1d800546081410317818401609030601007070080385030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 744974028 1250 744972778 744972791
    0x30403082a0a060902010f09030203060f0621070f050a08061501020a06020c0105060a0602060115120209060c030d0f110d050601022d0610050904021201061526071b0303 74
    0x301818041989001d949164450030003001715039009146103900e01c40760400d00d40441c10342c0c010035990140100210045d540000c04106d0580d100b9400d2000c454500310681c1d40c0c400c04051b1207481d03e03080d2190b420260040f8401042c2d51a0407840c1e4010f854030032005091903541c00b003013040c12070307642070b185419401b54959800100710349000801600480308000b04450511900340800c001c0298888400c5420842c01401603c0c6042c5a0001400c46843e0a20039481d1800e0258003d00c15110403039400715000401d06410000070025098910090104001301500315910f04150b4140110b1031010060412002050820310790169401002c10b10413606035072016180d01c6091400116000e100d000170701d0f03a44102d81d03810804a40c0c411004150305019074600b4000c00c02a41d0301500007407141c0303004450340b0003e00003503004000070008104040001003002002401280c0030703040906044000c40c48040d1400740c0034000d80c0c0103460a94412011403107004d100008110039040407402c064440c034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 744975278 1250 744974028 744974107
    0x10909050d051e0d020c0f0610060f0e030703060501060207170606060304030c0b0f09010e07030f021203120f070e010c1703090f1b0901210605070311070302070e070203040308 77
    0x14013905000c460b00c0e00060750b500565128528014010481c0103440d84440708200098410415480071554641014085580002415124007220703001440d00740c45101000000e221950704002d041391025000d69207002e44400c07152401c040062052850395100310041203003404c00b03000456010f80645810081c4030003a03924803814800645404144500c14400e11002110a00c2004401c4203044004c3c01094555039803010b9030b51030500c0203441900107089170b4031841c5050044416007142c11849034941c2c0b40035a5031406140d0306554100000794925030884c42940100702511465400c118040120b04600c6411515540001e000391824080c02e80ca01d983c160341002449180f07112070900d240c4540e0b141d024441040030503406540c942094106c20300c1c01d81a40c0c1e4000c40140d0704400c1c0428595903c090a9024242040c02148000d0340003d0030810b0607804143d1200362034262032801080d844010049980b80594000540382c03a03004c1100d000c250380e00c0f000401c0003085040d0a0401481d03c070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 744976528 1250 744975278 744975337
    0x50a0e0d0918061706040203060601030b0a0b0706020f04030b15090c090d0501060518011706070f050c072706140a0902073801120308070c02010905060a0203070b010909050d05 77
    0x510741c44d402030b40100203000031460300f840070b1a1312410a182c2040003907001400905641c0d0380e8441c01c070720f807000012030700140305c03240e011100070f0100301003101d954036641e00d000315119604844000240405684103e2645840070141740584088090981840c005070100408050064021103040d96500d1000580d500c440c010112200c68141013500d01e50326203910068400120084485250001c5081221140c0c0242d00c16000e05c0782403414239110742e0054070003858840c00d0740108004001490503404201400031040c82501c0c6a4981481655500c105100440da41040d1081d40117400a1081c80400780b01d6001e019000d00480d0940310411303191492041410074000e1a0131201c03080e2048118000e00c0403020b600420182c3c1e40e0914589082e2001410b642c0d010b482d00040006034191b800640e8840c1b000c43d0702070f0200410840e40e03440c0da030f03030080d41d6940150811681c0d448c98000002c1d030b07a80781c2d01c20f801c0c0040d0400e01802c003a0000080480b0316a000341410001003e800d80c071014645682c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 744977778 1250 744976528 744976559
    0x3190e0307020a091821090909031e12050a0f0b011d011214090c0a1202030c0114070507090c1d030705150c070f09050105190306020c1906050a0e0d091806 68
    0x40304424103118201c6c0d40002e0500846412141c2d0380d508040d0410000b070751043d0340000745002c10021401110740e66030104c0782c522030510707c4200142003c007441150b80c1d20380e1100205c1c40210f175040001d80350410041da503100c05407155a1048951501617804c55015003503420031704084800025000c5003050400d052040d0540302c82c4c2d01540310a6007083d89043c00344080c8081c0c182e01c040100000607070390010f56030380651003401c1d0400041c80e101c070486622141c10340d0241c40d03105003520105038941c07980d84018044c6220300d10008280651200450501030100901510098080c140b114204020701002c0e41c181c06011808000400c0710441c07181081c0203040180034640c1400c01c1a40c5084200d00c10740d0010307001a032080245602440000324103a407120708680c0d02c00f902580750740864180c40c0c24020407800c88030841c2d440868074010490700d6400503102d4010f4440807c00201d050407444d55410b00c4050300c01c00b05083c8041405801980c04440d681081542c0001c60b04907261541084840380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 744979028 1250 744977778 744977813
    0x2040929090c160c0f1208090d0206040302040509011e060f0e090f06010e010612270212010903030e010c08061e0301150e18030c070e0a1103190e0307020a0918 70
    0x7058000340102008122100006d200100e0390070b049407055114420700c0d105000ea4580300c0c03081100746000719140d0700c040d60021500103008005910303141c011640a0841d11207030032070414034083c0602410300144120015541c09403d00000745003801014071440e50090706150302031082050b0800303400d10810840d40031300072154000b14154135054000d0040d17400040861a254100394142c2c0900300444000c42d9654403040075500381d01d2480c0086454a00e42e225a01c0b01942000c03100414140c040d002010041e9020008001500220700102c0307814400369503059005022404441204000150102c3c1e803030340c0200001411b500c0d0b440741103912001944180d4982440200b00921148803c8552051146d02030155140025181c2001d480e4005801920b000b50340140106031842c046900203110002003981041c1c0d02d062014002c10b8a0300103880101d002c5003090200c0003e000040b06440205134080c2c070184034603040c9541c0d040549241c00d058411031110240c0740c2c02040418002011042 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 744980278 1250 744979028 744979043
    0x8010204080d140a2a0c090209030f03040501020601120c050a0303030504210807050a0e0a060c020a08120306060a031e1505060705210f0a0302040929090c16 69
    0x21510b03001600c044440035185000e50340c10310440d407003d60071150b09038001161280e40701c0640f40030800180c030500c42d442d0280c038203a1010b44c007084080f00c95008240b039000480898611151100b40300b43d491040d40581030058000400400c503600c0003058100000d40f003001c0c2031034010b8a50380030941d207540c41d0780281d000036115001e100501070248106000d5100c0000821085002d9100107440030703101404036000c0010020310014028407400603880204002000c0224150b9150b40c001d0417000e01c110141c2c4204406030303001500039000100c511071517010707a0802c0d046980c0c50040002d1508801b19060a054a500c848400e5506d0795150031071454541c200011400e464050300403803401290441c90080b9020018080400c40c009010150b0012030310300c100b40f0720540031000505005044c0c40e03080140c00410480540ca0f0960007500541c0c20102d4104511207400c0c0d241880d1030030341c6d4451b192101004903541760604060b4800c90f03002030400c0340113182003240d4000c0b144504480105a4000c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 744981528 1250 744980278 744980293
    0x30c05160f0b0610270f0f08150702070308130302030d0305090f070b03060d0f0b1e060a0303050703080a021b070512010c0813020117191508030a14040801020408 71
    0x215150807a0807050640b010502e11208002c0a00200f1484159100c038018240d403140c0f44941e940d0001d0040c6c440351020155080d900c8005038103003805801008a03c0c0191414404c01846c0030340c07600d00c100d40550080c10480e103152203000c0281c0c49550403d0242010070008409614100f01901402c0051394001409141c083c045d6820140486d040b17607541d8029050411052408400381d13500040c040300c03d140c00c00381c0c910740f041076100381100083c8200c0d02c081c100168001c064401300e20a090642821050342d43c0c2c070040203116051400000c0200304180b1260000c030703200e1001240d03c410707002c81c011310b040c036030030318800080030f08281c0c40905901054052145041c5491010319a0088200030b002c081e002c01409820318800508588084c0150821007081d60b1040c8105210f030080e140544200342403640d54014004a145505041d103030030a40890f43d01d450407070320b800c01c03980728030081e40c141a080502124014040403e280010006100100e8103040070b2005000400c034040003040d00303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 744982778 1250 744981528 744981533
    0x909150310050f0a0c050a050405130212040503071203270501290103061d040b040f1e020913030f051e04060806030d05070809060d15080f0f1c030c05160f 68
    0x40d11481996101003007007d1094a01c01500f0000391400d0ba001202c01308041c8980313800f1030009000d07007600c09034856070960030700c424840048000d08201d8007807042103110381e10055040c0c06841c0d0300a424800841308c0c01c211422982c03481e00c41045c1038401e10001c035032030311165440625008544080540c1000c0c0300305003415980c1600c0781c00e00a041600c40341100d1007001c041100e404000410203400da440d00400107081000c0e210001d8034150b400f2104104428050080140c0c0b80412a07040b130040d5010301c08191100b240040d0300c00000d0f030550340c011713600c040c0b03010440c0d898020208800248126035041c130b41150a4001034005015195034081841c40e2040c101441c111004039024140f0404000040200c0c10407002c4039005d12050300c100d80ea41d003884804900500f000d0070304131840d10303e006001c81c407070340c1c0403c069425030300da842201d000840c49440d4076100e0f841084c104107410390011321101800d0007034129030f00c1e81e062400e10230b080451245078040709040244003281e403c030103094900708 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 744984028 1250 744982778 744982781
    0x120c0c060e1816031d012c0a20150f1e0403050703082a07150e01050306150c150702070b0f030a050a020c010905100e01020909150310050f0a 62
    0x2100010020010341e5814105204035a8004941d405010180c840d208200d41e1440320420045c80034001000708907a40c031100403400d401d03403040d00801039118004e00c10804000f0002c1d00340495904103480002c00804164400035418801c1501384e0400000380c1107111101402d805040c58042940045a41310880c5640c0b002001401c0004c0e40444400d0000344081080014000241c0394844291642e0310048002c0034244034007407006c2036403000c201d400c5082c2c0c1d0b08042031260403212900e010904c09000903509880c0b40d40f2108003030f40001c00501c00201c881c5400e00035907505030003800c0d46c90f261000101c1024100034007481140960030070082800b00103a0304101240040c000c40c0d840500b4140090b084e10a42d20015000701c0c1c11949400209030141e8599045400f05007509008000c404080e1520f0303a01e40182103000c0d4410707440c02e001c41c0c03000107041c000c84140b03400007400600e0b2695245042e00143c2100d0306002d401d44115607082c28000d40074071403103000d0600c0300300a584900d03264140e0380 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 744985278 1250 744984028 744984049
    0xe2d030c27150405040f050f0601230f0402071a220b060f1201061404060506040b0d110a272702190905010908010504050a120c0c060e 59
    0x14007074541408078200e611032802054921401c480501481619002d4001c610306240a80d090750103481c00d014401008510b80c650407a00e4031950680745100d1000d00101d0b2070350030034403a4140703044c03203410203800b141d216220400e00990b0083c102c905400150740860100c3e0040c0c8011034690030f030710115680016401c04480e034021818803054118103444026094408101ca4004100c1c500600c0440d6856403a852030076a800e0300036201c3c02d8401c40f00c3e418030b8040c0826200d0860000101200d5a40500b840c1c05080b0036140d003d000355180c1482d04116007180d41c4500100015241e4910154402c0c001401c01045e116040740c0e44e410103101d80800364803007155001c8450603c017440c0801080420342100842071001403210340d0300c04524801203104068407841101214842801c400a5074803900000003205417207080e03941a0030304d80c80b0705200d4229034040c1c9014040d54001041346000410503914841200d02c580f411113070042d1166625407410801ea00300c10302164100b0401200b80c01e00800703c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 744986528 1250 744985278 744985303
    0x801051c0201050715021c05072c09090115050f0d0212121602010e010e0907081b0c01020c0c031603061104081e060601020d140a0314010b07030e010503090d0e2d03 72
    0x30001401c02c0d0001406080b02c41100c0b01c0d03419805985207002440216411002b0800902140b08070b2070040341260081c000c0c402c460110221140001c126400c10400c4c06d044800301034080015a0200e40030000c0303c40d201c0750100218400c02602a404680d003102901c08582e29a250818070030b00341c4005450b0f003158101803410822241003c4045507180b100d42500f01601e030410040d251540315501002c3c0d81d6038070410110010000f808005a00e05500401d0b006031003405440070401540101511051001030764410400d5907001800445c0c2941d001900b004441044507240c9030303480e05032500b0105580701047d803080c1040c00100099000b400400c0d130040d03091016142c044104a000b03030070310b003010152029140e0040380d64a0002e009a1243c0c0030744141185400b400c1d03030f46249070501d40d4030100c01103002a043c041d2030760003540a001528042d544890140000c110111000c42e01c2c403070074152256000d2841042c0e0308550080c0075202d49540622a056014100c00300c050602d03001141400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 744987778 1250 744986528 744986531
    0x20c060f1909170711240d020a030617010e0706030b0d030e0f04410a0510031407030c0f0524040306050114100801051c0201050715021c 60
    0x3042841c0503000354000041d180c1c074000040215581c2003a5042c3c008180c108581c44000041c0c0c141400541800000078090403280100b0004000040200345042140c40864424040c01000398130007858028004000f901d00c0c0c0003032120341e10035400340c550405580c441d520380d654540920100a091107a68007030101c0c1d003010b001496001000c1003004466010103810007901e1300b10800700d13981d180710130819044000e0003406008007001e0280120be50221003d42d0454030503c0707641041011031101c2e140b0b4144120f0450782a07480a15100240400402482c00c1440c0e490010000800d01c4140b503040814070030003056928110300c1d24580094082d00035108050250b00100050303941c000010180003150041d0000a2002e58040e02c101d00854200a0110f410000007080d0000202c0801b00132031001c466416620148000030340f003000080c0683c0ba04412803103040394441c841c603035a000c1e0380e904c1850701500c0c0c0788564403400d5091041d800c120008079000552a010221400a007101103068100c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744989028 1250 744987778 744987781
    0x30409050103050c1f0f03110309030a0206070206091005070c060c03020406020708070f09090f1406150910050108100918050c0303040e0a09020f0d120305090d0905130e10020c060f 79
    0x414a0006040303a00d410412241c00c0c3c1b4070001520a8000da01e20009001525407a81801c0403216281e40003602050014170486000900d01c5100103465801409800c01401e1b8030800c0585d408090303c4024083e40034800c2400d0340c007001079400d10580318032500301d65006840e103062032002810804aa03000f4403a65015000600103500d064152400b19000d448001400355458174201081c060443d201400d81e0f4030300e0480c84102c02d4042511071080104085d002c52040c462410443c0e140070907107400c0c50341451003400b80080d5020f4a900c40d0001c44c905003c41e0142d549071360f0b180584440c542d0360809440100a1142003001c10007079102e0070300e03041340507600b05824816899411400140208100742d00c1d0200e010079034840404552003c3d402620100d83d08260b0306020306540341084003100000e2500d0700003029590b010038000124021a83c400390141d00e420201b0002140f490341064400b543c070441c0c0c600c00a010004400780b41c9602c0b50158680781d960340d4050800310010300308420ba142050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 744990278 1250 744989028 744989059
    0x711040c0c050618010b1305100b04031e050f03130e0c042103050d0f14010f05150c012a02010f020f03270318040b100c02120f030409050103050c 64
    0xd8015030040c01040101c6052130000052405020f03031400080d0006070110441d0101801d5030441407180b0b10205030035040035580d001c0552148510b20020b846c107040b511448400c0b17010464403154281c0210112006004000586e9007983c0c8454141c0d00005140c6408103c0e101f0040e1489a103c00504070050070207180820780d02c0d540107048201c00c414004071120508060003401601c01c5102055402c000c515000003406005001c020000d52203d00303500000107164603440c420034203450380030301400a4141400c4c50130019801840362500f09548a032190f0000ca1040720b4090304130f00300d04484001010f0f1440c0041d01b1141368901042009004020b144110756414045940140c5400110705c229038a08454070241e10241c1001001c7d400000b40329030640c20185106c00c040c90003210100000c0241804101c44031036040300000c00700313010700024405031416861140809032050190f40d01344030301c0c010b81415680281c2209070030560f03c400500910038100400e5502407001d9800d1721f9201d00c9003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 744991528 1250 744990278 744990283
    0x40501150507170d02071a090c0307150c1208042d02090c07140c040f060302030d08100801050103030f0e03060708010312120203040507030314030411060f0903030711040c0c05 77
    0x10302015110101c03c180d01c80007440386400f182c000c8601346000b152103402628101c0300b0101d6104962100c420b4400c08502c4100005c0368015140302c00400a00315145411b0b90107008600403032101c070038800401d070040003042c00300381d600c1003140855941d4103103403038141380040e10b00c0791160070051003183c0580c6451720344410420710305c200f41e01241e0454040c0d455550424803072103801c00080c180700d50260300140f80007000603e0344074010308031001d00c1801342c084960001c907440341c03102035416030004c00f000450500802d0015080009128411141074840c958182174400a0784210300240410524010081c0d005803034011025045024104601380304500a2140c90180409040318802d01d5003450b8050040d60522101000c8030810b6441c3d20f810b040003601c0360480e2009a020030490103100e401443c018040302d1159a00c004942c42480d4224240092600900c5030b0b1003031120104014525580c00300040d04076203206505c040e280c10540c07001c1c0419600b8101350842070000da000c0a10008801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 744992778 1250 744991528 744991537
    0xf2404020603060f06070f020310020a0207170f0a03080103020f0a030302210c0d090504110306060d0b01030b040614040e03041208031e010e0109050615040308070c05060d0603020405011505 83
    0x1121242d4407030700d038640003801484101c80f00720350203000002e000c000c01840031442c28499000301c080e00c001f10007004030030b170076842203499200058001c00001d0011241050350701c50443c09250443c0c05118000d140300c3d1500503c00029400304800c03100400841c0707003804d50f080c16130390207503051141a440c65401941d01c07c1013002607000710844484031a0361603138078003d5441c82019242220255001210702810452841c010640140c0c2804000640d1500500440c0c0c0540c1000d455240f078086220000402003046041d4141003544440280017030707681390300821700500b80b00600c1904101c1400700300021240022650351854105210401c1070800c180600e41d202034100300070503038a0b41c40c04407001c01d444110148503074880f142d0001040c400c3e46080c82d141600c1014504102139101c24040184d40c04945a205862032400c0005100103140d60001e008014803c00f19003008035100e20000302a5000310403198401030b178803c000c00951400e401110300402d031501d040c07051910450340c0140345104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 744994028 1250 744992778 744992783
    0x12022107080d3c0b0406050d1712010b030a0b0108040818060d02040b070b0106080405061803120406022106180907080d09090c051603080a0207020d050f2404 69
    0x207403945907414000159040b0301c003c040700900303445001c030a50002d07210910045042d034252071504500c00701c141058800d0b10107907240281045100c10313460740d5440300d00030400240d40440b903092014041e0000740d0351400e8003034401a00ca1684904d40149070000f19180035a12504010300c031300a20000c5422981161442000241034008100c42280030803124410207000b090503510003e40060790f242400041e00390320f8815000c0d1070144c2d0f46c40c10100c941e134070240c90140c215000030000c2403210000c0f100c840c5005400d68240da0070400d40c48481c13404000d040b1303802c0d036200b500000c800c040e1384a11001c44910400c0d801e8082242d0034001c010569040f44048000300008c0b100d80802c005450030081c12009004050496050002c1c110008000918911034903007014107003403030f501205006000b40c803080c401740032241232030109589003145c5034400913240402c0d45508104440158944000d104280383c00781c0c00400e034841c09502c5282c6452003c075180c9542104100c8141c8504103154030a5400a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 744995278 1250 744994028 744994031
    0x10f02011a0609190e06041b0203040605031003050f06040308100b0f0c0f101a040b06030a0902271e0103020a0303080a1e090201021507091a0712022107080d 69
    0x2000401282c00240364031849020a98015400a40a8021500346104000031f850504c4116003444800807100d54a041c00c401581041c00103004180c403032006140d110210700002d166031907590300e80d44c0c20101c00c41c04542040c0c01c48000c0109150700b1183c0700da00070042c81282c0071340c2450305074a404207000c0d81c00380c0480d2140c0000d24050140003017154840400d000c6048e00c0c000007006e0880070040000718848501610291042001454944110b0440c02c1d03001c3c0c2054074643d04c0c0c0980000416030980c0490384850382600c2540c04d4090128401100403c40805403114145481100261001854501100e4002d840144016165084c0c1c9104032541800c2030821230720358144c204041c00702060300710160401046010440400c2e50442c4580e24003e03002e44080b180e64002c04441001c0c00c6070400c0204040000800003080c20000800c500a6007a80305401d20be09591112031a5215140001c0140d00c810784068000030f03107040d007280400901130040d2a05900356a004010700a500b2003c1e01503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 744996528 1250 744995278 744995287
    0x1b0c14070b0a0f030606080c04030206030615030117060a0603050c0910090912030e0c01140c03070203031803060c1c050c0c0106180b09011a070201020f0714010f02011a06 75
    0x4000801002001c0c1001c26101e64540c02c010000424000001641ca0002402d0040001d0f14601660295000307024220ba103519107801c54082c07100e154406000c5a4008114008070004403803040041c5010b4285145502405d516000d100d9280c418041e040c41642c5203040002c00000b580010403e01410b0107550b082d855030707076803100c01d11044400d6001e121134505200380c1c4800c1203850090b400c01c1e6149524200048020007401550f1140f6664003103010580c0a500903100c40d2084c006000e4010760407080702e2401075151b02081c2035400100a4540081544410712410325080c0002039100b141c0c00710b4542000301c80c1045c9802f81380c801240e801c41a95035800f00d0001401402100c002d149004024040d0b6035a4101841c465103021130305010040c07034001118041d10380442142e0407904461840025808600e00c114050ba001407002c0b41944152006800d10722010f001d07000080101c3c18a08c491600e86000140040100c0c5007000c045914007000340c030342d10301189401c1e506240e00b0340714103456 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 744997778 1250 744996528 744996563
    0xe1501140109080106060801030606080606031e10021605060106050304030525050a0b010e07030905071a0417060406050c030402010c03030b01020f010f02190c02060a03020307050702060f0c011b0c 86
    0x14032660b08500f4095003081c601040c4540c200700218101da104078000c1158507030b0b80d80a0341d07c0c0c00d0203841c413a5058000480e039105c01c04004402a900c007803280300766003100d640180480100d07407003125412040034142d280201405000c0c0301071401800301b0b05220303145240c03a9034010900d11034491003641090041f074800c0c10040080c0958410180e0100407141c2c00c0c1ca10b801d01000900b02403140c4e076059660340001402007407203070080c1c0c6800b5a0110051540030306000c2e104003400c0000520b150141010301000441c1e109860580a40141210140a403800c040c28041c0503110001c040d017001c80742c01c1050100503607100e50824002600b51034000742a0060b000103e080c0080000c41c03800d85c3d0301b085400b14421410754000d165101d81d100101110018500090b1260a4a5070019521040500007005038500940040da800005440c2280c9080ea40d5400208650409000d00e184410041510b6443c10400d1090781c04030080c54200384030404481000402085200d01c00400244940401c0e240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 744999028 1250 744997778 744997787
    0x804151a090901090b1f0612020d11070c0b040e0c03060a08030c07081e03030c030a0618021903050c18120a0308070906050f030c1b0604050c040e15011401 68
    0x3522401031000403181010755100c1c0c00703014030303c80507074820b4160b40201d248402d25807401e80311610b40d244031624003881c080c815650308624445031890030781c0810482d01ca060348d912400054508000d10251210858100441e807040c0c160000c03d00401e0400003400a40b002c0f003c610780c0880301c102c1c915030303035940e1001041c2101c030198407004640c440800d060f800380b0404074102050300c0e046003ca5107804c13818040d880b60002c0d00304003c1050342040021079400e00c030141c02164490403020f0041509652601c02c240445020f070062007005074049041303106400303100f08490309028289418032050400e00c02c0f2011070700c038040102c088280307010403801c3e050f11030046103a00c0040704400e5800200080c00e01070607692040320070500081c104040864054010425515009526902a8210743e00d1003607541050340640080c03000c00703614a11907040740b90104034144c899031044024080c00700f41d0780c00703000681351240c2c10318650b42c03c050105038000000301200c90450341544548141000207034010395 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 745000278 1250 744999028 744999071
    0x2090603011809060c09090c0311030c0703020708030406020d0806010c1a090106030b040c030303060b3c0c0d021216020f0415061d0609010e0d020103020d0e1c080415 73
    0x1002e039410a181c800c40240c211b4121002c8400c140c10a02070345000c40c00481c110307424081d445902510900101e64100094801351000d0751090041718045522030030a02d03e10f40103680300304c0043e4010f0300710a4000f035209424980015080c00c0c1450070344102e030341e40c090000f42101c40190040b408000101c0c0c3d10800d4209000440d08480f09103070030b04190404403049042408240c0121341000800116508030344215494030300c80b034800352002090344154514107220700d05040040d100d0514800c440f0000140140107281c031040040516280c0100c0180c14044590130f544001041842409154861501244400f650403524243c8076171260700000c0041004000b00400c4907507107040030812541050200f0783c011340242d1800d14011407601045090301c51005a07a00080c60f40d44415441e091510712040c0301441410003504102644072a5012a03c0700320001906604c040f44020310030010350f022886001032440e01c0000b61a160310760b10502c001c040d441130815542c500f07846180700031606a08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 745001528 1250 745000278 745000283
    0x61b02010f021914060610050f0f0403080309010f1109180901090804060c051504121d2709060702030415020a080a260609010501120e0d080708070302090603011809 72
    0x24491080c2600384070030000c00d048480c041303600c1380c6070208801e4a44400c01041e080d06075a075561a0050b151028856600141d0345481e51200612001c8005504100a1480380416000002d00c160b00941c1200641d01842c140445072a0108280303c4541c07075228429100c2055180c0112aa403103101d042401040050006010118081800714100e42d100d8076607844079000c3d03000c503086550f400190346a166401da400500940c0240b04000b0880d01074014642201200d0584a280610a0001c20b942d14a40b02154503440e252080c0001409002e14005820203402001402c0c2840d1204001e903a0b84664020a01011101c208823021070784208540c040195120b02d502d6280c00341d6910260060b9007c800414408031800808070a14040307840c024400d007401400c0703036200c1c0d21300001511907960840042c01210f032500458409154100b000c905404125035411040b450003c02c01420041c018142d401003500400400000d82d45e00401d0380c1c1561842c0c10304a1b0460f074400399000c001c140e0240700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 745002778 1250 745001528 745001563
    0xb030a02030d03050709060206010b070605040516150f0305090604110d08040602070f08160501031805010501030b0f090f0a080d0e0d030b0307090603050703110303130902030907061b02010f02 84
    0x800b800280c1c19040140204119291521069102e03c1c0503a1140400d019846550606200c1c00c00814a0307070304029081030041040c0c03200103800c00052503034510141c101300942040402030540407940034007201c2444a06140030489810f009180903140c10000d0009008103d400746114141d64984450308e0490b40d0140e0f90f0755569a8440b0065103560503445550207500348128005110032000c502940c070309803207108241c82e160400300158014074655140d0010f80005040743e40c00241c00f445000c6c00f850242500104900d00b500d07220b500110010640c600e9504040390521001c0c10004102908552000c40e02d03403a44002c6602e41300900003818054654811508039034111901a0b1004020301d00c19000d13141100d86410960081d5070040c84001d000340e01c458400c0000c40c4616088815041e4024180ca1400aa107030089855841c190080300940c2d50000601c5050031041041038014541c90608000300078003d09080c0203802400006818010020721480c1028800e2210341d00454501e00c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 745004028 1250 745002778 745002793
    0x10615080f060109182a0905090a1e09030c0f0f0c0b130611160308030a1803050702010e1305090a02090f01081207170301030b0a05060a030b06040b030a0203 69
    0xd00403242650120807800450012a02551143c203030309094a4030810000b0340b9041421a140c01445442c101c03144160343c01240b40514880348040d151800318035650039490740c2c1410204206d20f0005440200003500e01605e03519184101e01c00340c01d0740c60314030300b002458100c18203054680e40840b43c3c2c0145140900c0b00810100039480401340351150068010140035034a50b50b4010485c4100304900c40304402d060810040f03144142c022030000c201840c181d804c0349482e00c0741a048031900d5001182c002c034010081120500c010312526616400c0c41d10130011507c410b44004c0d00910401d41c0280c100458075150041c141c48613501c001d884c03200100100107500d88102426143d2889503001c900c41c0c18808040341d511008900d400d81a01d06480c098140c070303441031068a1180d40006402c850032849080070005052044000c0c41c0258041c41041c516403a01c551200b0031100010071203403141c0700c101030a102180c5034407501d0b0340c016403e07100025060802c1d00002d14241c42808002c0d4036101d102c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 745005278 1250 745004028 745004069
    0x50a051608040914070509120c0904060b090a06030c12060b090406051605090901060c2303030a0f020319022b0b090610020d0c1401020c1c05090a0312020106 69
    0x20700a008803116841c08100444031580c59040002c01555614001641400035250504d40180b01100c00d1444c141140c02001211002c60740542c011502920b91960b00c0c41d1f0445203081c00220030390b1000300c1c01400c101027801d640d030703201c1d003602580681101601030040c1d020420802d5404203030740c400020a824039901c1c0900e04080034100032228020034400303070311030703211003501034070549021450041c100f10003030f0308041040b100041ca03040d080c1d0b1100809100d41e050b58001c021104210117018000d10358a00d04000d50000796000c1c06003031251140704200300805d01818580c40d0181c21009000581d03034600001484141e1041c010360101c00faa0016030400d100b800c2503020b04203440059600e18066134440c0304000c125030071450300ea03000d07800600140100038800c0c00940c801c01c2c8101c1284016500014526003240c100511074a40c56000c480090f003500260710415860740341d00e00d083c41c80c0a241501051000b45c403031100510250108600c0035100d4000e41100c8090400c0103c2c5512014890 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 745006528 1250 745005278 745005293
    0xd031d0d050a0525050f040b0d20030d0c050c010e03030c070605120c0a020601031b120503070309090608030405040f020706022b1b08060f0a0f08060f0106020d050a0516 74
    0x90f15613500100391140f1401c8280003000c00c0204460f40244601c2100040c84140409896903c83c580c0d402049094a000040d04802c4000d1f01c00801090942c40303e04401c00381841c0048118000307081c0f2000701fa2050002c0c00010318000040c000786070052060764094080391039401010441c1003076004030100441e4840d800790140c28900d44641c0910000d48171000410020710401c00220016000240144013181d8102201804c440745040601083c6a841d4000d00481444102c01c58650b003000864805060780510352502810140c1c000b00f00300d500c0e0028060396489548030351030059445003890050b083e80e69060380c10b019007000301503695049412400d10f507000c05003040718410440030042c0000315528407800c084030707007000d184181403180c0d4541034a103181c000b00443d500400c102c1d138a82141d1504c0e0781c202d000f09610501050403c0c1410b800e6402c14000174809280443c4640c0100415030340010010000110390421a98036034001c0c104903041d200d21030450501c1d20000f000e100c200201c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 745007778 1250 745006528 745006543
    0x1a2e0c211e03240b1204030e030111090102010b120712060213080a02030706020c01051c021603030b01031802030304050d0c08030f1903090213020901090503100c08060d031d0d050a05 80
    0x28442510341400c074000141e800f418142c05544074000051002c020340e0030b48060701c150060b009003011001b4220881c0000d0966803030b20b00444290f0000f0601001c203580900500c010b55808480aa00c890020480d5544c1d8080030312400742130030480780040090100550441700da07080601c408281d095200c2035026039414804404074041d114618000035142d10100e000200460165101880d1040b440c0500100201d90ba0340c004103a9803c00903000c183c2088030b849a143d5200e40c902040e015400c10024085455100a2500e60200d614030440141d030302000321801d80d081140d03001090107a0741042518916560402c9410f0b200c001a00d500c52200b0300040c042800c1c071491008012007819000710242c41c042c0307030001c0d044030840c00a1b5a2006154000e420290018904140284c2da5800020b280030138158003010f0659031070740d948603416804404160700600540e10403d5029003030f0b4006101442100022200700322003550b02c16642c2d40c60400701081e40c0c000040301c9200203d8100a40c4a080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 745009028 1250 745007778 745007801
    0x1804020d0b191a1507030504180b030d090918020109030b0a09140f010615020a020d061b050d060512060f100e2806060c061a2e0c211e03 60
    0x4c00201c9444480305950440340c030139a2654405050a150903440184450445240a60340b40c581c05d04102d503031002c01c400d18615480e039a0300802507103020642c00494202c00050608101003604131409070340c003c000c840850341e0103000c0403040e03580c504c1c0140c010040d6501c020b020302000c0843c00c1c2010000038501d00c250000c040200421940d0711410125408406066030140e0041e0f0b68070405071410b429003400f080c1c05407401080c031b416480e110140c03403005140c0e5100800c1d03002c500900c008103548030f1680682001e58804006139840140141da0750700080c0304142c10003036900050020110304007140c0040101507261401414900564604854030030b40d031024402c801c200484450303c0324020002154041d498480d05218036031541c0b0003030f140210444281070024a81503006848a020580383c0e81c5440c4503003038040400d2050b4884528000c2c0c1e80c0c40c00c0003409490b540c0440c003004081500c407032880c40b88040c00804104203880a502510f00c0c3c10701c0f200c000c100070305504c0e01500a43c0c95180e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 745010278 1250 745009028 745009039
    0xa0b030609071a031e0402030a0c09200a09050603090a02100c0b10180e030c100606080a060e0a0e0a061401050f19211b051804020d0b191a 61
    0xd844441c0c0d400780d0004a500340400c1d1750342680d000500b071400020719001400901900c1c02a4040e481e070b0078000a1030f074019a0515a501c0700300d080c12700018a5001344c411401c00940c039156017043d0003009a185401090310a070740020120701450410000c03000302582c080e2504006204245014000301c22030541981c45c400380d200042c07034940074202405c0903500c0c0107614a0311200c00c0803c450080c818400d07841b9991104011050312601d007081707020310300c04440901089081c02c1510060401e403019200c0c07444681094014406c0b4424451010f9100649010008020401000032450700326900000b40040c1d01c0c0040c0006002003c8103010b0607030700240c0c0c0d82c03021050018248206410001c6031203841c01c00d102414040d0b01c100340d0b17103038150100d00d4420040078400c2c2d441e183d07506148c82c52441000c48400310204440c1c02c0400380c003a140031840b0840d03055860290040f6600442000004060f00c044c81f0000d0401005071000d402c006000110401c41011440c00008603502c40d160a80c3c410b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 745011528 1250 745010278 745010309
    0x6061b0109061d060c0c0102040915092301050f040906020d050f072f1204080706021c020d0809191a01080a1a040203191a091903080a0b03060907 64
    0x246281d00307100d59440d0000091465170744225540300c2d150460b4004805a54080000040404081c000c1c0074083c0002a83c1d40c105902d0510590100c1d2a29031008052b54042101030a070303074100e0000281192026540381c03880c10340c15000980200701e50240102450310104e00d6001b0301f0320551107144640c2c4e0840d042035480e29649802c1c0c03108402a001e800c442c040300401207842111105580400c88410402c96005000b081c120041c3c0d030700076802120280d8851181040115410411150105120706e240490f00c403000d24001e4840044200765000c0c006100045481c48200704108484403020b6041080d1404080c0307000c00702d1007800c40d112220100b4580010a40b0300c03010504112555001c94010503e9407000500c5401e6072000b4416a8540181c50701314400022139854080c44602c1082920300300c0d80c189120268402c0c000e051a4001e60009204001c174450071451124031030b406080007610341e990000618007030800c412900350940614014022031480020740308059581f615003d840a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 745012778 1250 745011528 745011551
    0x1d010911031207060e010f02070f05010c08010605030c1c15060311030f0103140a0f080703020d0207030201121d07031202072301050a02030c0616021006030b0c0306061b010906 77
    0x1c0b19400c45524242d14420004000000d03583c0d445810a003c01d180080b42e400b100445150132600a2041a21100d103640e854404004080c408c14602030521b09000c407032541010390051030b0f800000c001c41304400c00083c8060304d03a10720f07201c0d4924291117900180700c0381c903542d0151810480b0f1382c85400007090910000342d05415200b01600d01c95114103400c050142c1c07a644406441c0300701c40d06450303514003818001d1030210f88641e410b002980e000e0b0000da69620359600e002460903841d07804407821504452002d10050b07a2060100800d04030f4440c0215540110120341d120b002450103104210f0f21075801c000080080c20405048051066003e54000950300d1240c0d8214009809040e45880310340005800f1644c040e40207402c0541491041702d0800013422007041c039041c2c0030303114444800c4031a141408195810420540e40040b2241d06000551540c0d89950410364060480710001c0741c0800026002d40714101030715072035800c0ca00e210b04191944001c80b80205004402a030f60700782000c486012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 745014028 1250 745012778 745012783
    0x1d0a0819020f0c060a180e06090f040b0c180a0e09070f0605090d0c1d090f0d0c12020c0a0314100c0e1909020a080901180f0b0702011d01091103 63
    0x40c0b0302d90034001e0b01035a00707550200606544541d24490500c12085ca4a40c3c02e49542d1900a0261100d80850107003800e01c00300300007038501d0050648042d50200d03420480052000603000c1d400c07000c04801c0988030b0000450011441d9078100d000da4100d584810001010072036600b045001c0c07c4c0300015501d5498559100c1f19400429000d00340100304204422211400d1101c0b0141c1c485009a00d5240002d440d0850404168101d00c1c094905042a0381030000021060013400060100c2034000e140030000c800d0042d10601030240301030301035146140c00300c2d80203009100c8035041c2207005140040c169104d25195609a00150048145218241034015201440c0c89407001580d419207030051405030385000c2101c54103a624111400d111040f50002c3c030050b060000e130003400441c4c1c80d843c106141400c0c056003180e038400006e800701c400e16001080407482d1060a03070b10542c0c02c400c4891582c3d4502d0300981c0581282c1800042c104c800710800d0304c2000040d4425441184544014030038070008104059 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 745015278 1250 745014028 745014043
    0xd1a0909010b030d050a03060909050d030c1d040e030702030613062d051321021002040f030308040503090a060c03020d02060108030a0302070f02121e03031005041d0a081902 76
    0xc0e0560300144144940318054005004c0980c8541f5002ca0320315103482c0c3c10380a80d48040802c035441c3d0300100c00c4080582d010301075070251224a1070308450781c100b5140c6001e0081000c040320760007980e03030f660389100681044c422a5903594010301141c199007802803101280d01c90081d0141e0348245861300c0700c0904103096500c4060f0983c0440c45903002030011015000400c00601544001c3c2540ca51120004400260b440491030f1201110700d40701000c964042d0030a10182040c2c40a0340c41000140800141d032400d91043da40c01d1703c1d040c9200d9403103140051540c452040310030b41c000e2480e50001001c50740a038401c480075102e54281c941d6061400d000740d035074101c280903010064000b4800e248036240700782c2c007501d03520340608030406e407e401c00c0e00450000404011102d80c9500480d00300003800d81416613212503a8040401540755142071500c4141100e601e0145d24070582d12035a000a803520f120b0a9010700c18200005c0d034007208600d1500e58641d0b4400e90a030301c40441d0100311fa247c442e0001c02c041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 745016528 1250 745015278 745015301
    0x1b0312050a020a032f06070e09060a030b0601020703330203070905191a31030809131e0e0c01080c030402010c14060114040606050a030f020d1a090901 66
    0x786221992a134050340d003103050307861407403002c81c00022021702000d41c481c900c2c6051102002820a50911850040c070520747d880550780211540400e100803901c40107a81d00880e41c12040000d06030312030100403402c0c61031070b81c806400c0c0300c01e81c8072491200e818000f0114403100c15004010142c0e600e94807160590000b101c1000200b6400310080215061181e414071219000d4030807104402c2e161004030b1640c18400307a40c40b88040f408180b04a109500050848050850701403050382926201c285a400c4101404010a041c0300458598119100c680c414041b0034070840050002203100189416103104148100380307640c0c100310816042d001c010819403050031043e51500f075a5a0352401d107000301c7c2d0014104904001802003601c0c007046d60b0124003070000089401a1846515002d07065080038100c10f80244914909041082100e8011046070b085203000d00340132503c00c6c41198054024003541d05451265400d00d0180105c0c00c4907445101415a0104c8065078952115a4182d0032998192130a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 745017778 1250 745016528 745016533
    0x1413020d0b06121002040302040b0a050d0602091c08090a05060309070501080402033408030a200f030d140f0106050901051c09080307080f0921071b0312050a02 70
    0x3690082201030001e03907031080e80070b044888840a03051a9a140950901c82601c01550224041c411840c0c94000c4070f0801104450719a101c6050800080c440600800e00030f200c591300065030f44441d02c0c0c0520080710b03c514040324034a099060b0510800b5a071150b502d8611403012031501182628088003901d000d03400740001802d01c141804019501f0700006403040c0d07854400d03150412240008030101002c001e4050030680346034000c10304200c40070a03558001423030fa608140045020268040e000380d80f0040821030010030500c2d8401c0b07842c00c08100e5483c00c903d0b400001340034500840d958102249942e204070510090755100560880d011800780901c40010364100321400b17844d032250016116401078050b010000a01d90071180040b9018038800f25001c1d48088204100660000d250b641e100507814400111840d20b85c0d071450700c0d00c00c004400c20b00c06100e4000880f54910032010368620f0740c4d10100446e10800421a13840c40380c56144003c072030007039590068035030b43d82c4103105440e0001c2c0c0760b800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 745019028 1250 745017778 745017799
    0xe010501150507060603021509090112030e0411130e10050612010620070906060806011805011808010e070311030312070c08190c060c030c090902031810141302 70
    0x81101c2d90707403100c54240c5699860b44000300250b600d401c40d45030032115102c401991428582e00340403020105a020b0310270041d2103600c0e0004280c0190711641100c008450028040320854482c1c0100c1c02501c40700c2d14820b00008001c80c00001004c1014003440341c911182d410560b848041000f07d228520140001c40c01020040207070a00950302c4030b8040691800d18012460000c00242c54403200e603001c440d9407a00c5403800c10203682c02450350742d002902841c1503020b401d2000051000e0807840d02c540e504228050781e04041c00a4103c0c2008060803640c00288a001d404a6015507102850b002c1603540010a00740c0700c0061034000200e4100c072501400c0c3c1101a030f14280107a03849414807905441000c410808803555082400d04200720006a03101c1c03402c3c400e603d08100c1c0c00c8664150081c0180f606c1d200c100b08030140c100c1c4440040b20b0403444c0140e034a07039905401c0002c0d18029560a81a031180c1c41510440001941000c0720003441200600200e03030f035441d2000415461a070019401414142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 745020278 1250 745019028 745019069
    0xf160513270b0a0510030203060415020c0d2f06070c020a0509010b3c03131a011701110403021306050604091d03091c0609081b010e010501 61
    0xc01c994999042055181c094895030040d0201041019104990009860082000b500d10741d00c0380030b0300800c09110091005081d40d001c242e840e078020700094000d02a01603c0961603155404070358005d4a00b2080d18011240c03c0000350003000c09200032091011620842c2a0b07814641c80d031420340c040a000100341d20b844582003910141d010480590308240c5101d0040784540341c003c05c0340c2c001c0c01062051992a6440c3d510760304034440203110005400701e0030710b601c1d555180f001440e04c80350303108172000d03075407601c80209619007441c204200401070f209100f0308881c46104038044034103e5078174401c3d103250246440060380c200c800841c846034020380706103c103201500344480080d40d02c0381081e400141c0c45444a00240040c1c21507401040d810781c07601010300105002055081a26810740011401c100400000900c800c54860b01841800a401c4184041c88243d411249040340c00003011a07840c0760035001120b8030038604d07500d1030b00e41d0300744180484965030501c203640c1210800c140c8444516140b8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 745021528 1250 745020278 745020281
    0xe010207150b01051608090a0f060206162f070306021905040303140f0d1401060f0c02030601090b03100903020a0605010e4602070201030627021b0f0f160513 69
    0x865086d20300da2000d0048401c0368581c10100350203403101442260740702c2d1a01d60020f1030074500901581f0020801104004026000203c031003902503140745034002f003c05030030f0051186891440d0310101c1d12480c100041400800e40c0104541c604640340910302115803901581c8620039480020002010074901405420248001d00710300c28551900c540f80994460005040e0780e200503944400080080c010842581c120321119649003c44c101081e1410203900041c1c0c0b81c0d1014412400465251404420303183e90138411451803440e008810080700309035080c000c0d41c407548080212803091416001003880000011040d01c03034034510540c5050030926060031003243c54030025501700000e84c00c14000943e4036120b0744414800303005c4070050f11118140001800d4030099440001110106000386626221040716001d807203804882c0540d54083c07043c0502004400701c401100c0c0d40c042c04000890080307011922001c4070b0b48901c101c03410704510b0207107440a141103108540d400344e248103514890003001e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 745022778 1250 745021528 745021567
    0x9160e22051b1314061003151205070f080307020109140f01110c040612150227010509130212090304180515060a02150f0c0a210e010207150b0105 64
    0x180039002c0f20741c034000b520002d4030f40840704103841004504c10840542020030040c500c81d45949000d10a00c100b809070701107002110f0142c2c4503c0501d0300741400a00400304010401445038841c10402c4a40d6076444c0e40e2079401c0080d00321300160180d0300000360700340c146a40d101e29440043c8810704902d241001550316424000041e0510700031034896201c25a40d42c4604030060414600c00e1005074024504558215a1180700f044002d00c107002019403020448e1807002c0ba120003508002411a50f0801600d640c090105442c0e4407620140354000302e0f800701c1c0c0140a424189402c181e5040e201e61003480e4883c0a6401042280c880308440d210b0342c032041390001c540002e242030720307180507041c1e0780301240250780b0800408002d60721550601c0851449071a41d03a510403042c503d4200c50381400c007000c80303491013110400402c010340303022000780030f00e50b049224142e01c24030b5600700141c0382222411780c080c5d04010010707251111052a0040c90390054003d41c00b06a60507501c640c80c10020091100b0700e11130 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 745024028 1250 745022778 745022833
    0x2e0f02010b0d150b0d02150c0c0d0309181506050c0c01030c0f2708060f0907080307170c010e0705100503040f02101106040c050406060c0302070e09160e2205 69
    0x5803c03c0242e11451301c407000c100071f6003100b2990703902d00781390309403500c80007019a40c000c2600e032001c0720107c1d6122803240b00b510f20026603960111500502440a0000f1051001d040d60b807000c00001d903613802c4001819000c0d0a901550302c4c5400041c015021102e404102c90003007106038030400e4050744140080c90905040612041d03180c00c05544900b000c069075003090905610800c140001947c49a074035a9010f5402c01c0100b40e81070901c905e041d00da028000c4020300c40c07080900702c0c500000741b060603240c0e010f09250080020102100fa0650b680303040e8841c0138064080085000b00051107101107a01c115044241e0b1510080b85500780250a0107800d80042042007400c2000101c6005005035401540164040701506d414a01000220362030b41e40060180240000107a00294020070a5812107144450340c2d03120341e580c4190360303050a00b1800c60071a0340940b81c402140500700c440c504ca00800c00c5104001c001e615401c50258401501030014040d6407101d8490f030107030450482000282c19 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 745025278 1250 745024028 745024039
    0x3140a1505130f0216111f08270a030f050f0f09031f0207110a0302010f03050a06080f011a0321091309060506030124052e0f02010b0d150b 61
    0x3c0c40900700d408076005942c80600c50005c1079105418041c1c10311407510355240459404809020201001c0f0001507941c080105100407000051070403c0c056200801a40306100380c525040011000c080d1100300c0c0309000c801186464101601280c41603050b1b42100c0400480349191040d806040004c1d44c122148842d4036204145d00004002008140309140b181d01440260322401d403882c02240d1102c5800c02c5070700840740001c0420142c1c2e44001c5115400c0e51a0a00003141c0c0c440b10a184042c00107074212010030720030143e40c044081c205500105c009080b0000251081c00b140f01019140d41d921600104200e00c0240c0b4078820549890050920503030040c1116070b14814401507009607150003006880e52551001001054102805440710303071254113410702440c43e132a815084c0166060701415008240170ba6440e98142e2888e4241031040c00e0390000c00300e551031031050080039490307865001c40065080c00820300190030328a840095080d440440084003001208034600108445079269a111 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 745026528 1250 745025278 745025291
    0x22151d07030b30010c0c0c08010212040b150603090d0210090b010608090c10050403021e0105190207050913020a060908060c1c0c0521060303030604181203140a150513 73
    0x46001744202c20210b210340c0c861100c0b4105a0030104d0000030f02e07038446001030f401045244a22416203e150340d0060348010041300d203448404008403080224200d0720b40080d400401e02406034000600480e000742180c0c2118a1550041c4c080e006540c800c90300103100e081104014403880d4000c0c0c021039803111108084800030b070041c00004549807404801d100c0400c40008090080d800e00c4035100b42d0507001e10740c400b182c6a4984000800038411882c1d82100c114502c2c01100c4120701c280f001c0402000010a005001d00b040007910f0600107000104a208a0706440000340700c1f80107046500c2200c5041c000781115560303e00084803943e2200e10306942003403450241159406a0348180520500b982da00ca54136464181003d807014032003a40b10046400850040015039500001100d42c044c00543d000702c3c03d01d55080c42842024000c02c8000c10849001594810480c0c0c140c0c4a91508490242c80b4112602c8105c510404c0b82c090070490080e113240301070140464180029401c1180038000390000b42c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 745027778 1250 745026528 745026619
    0xb040609060e0a0c050712050706051e0c0a12060f080606030703050d030911060c070f080a0507031506030b040609051b0d0221010f0b0a050a0522151d07030b 69
    0x2d841682447e40100b030000c1f65520070b00085101e159400a0707041081d50015184598010106c44018070030810b1540014029615a03c40c00d1100c4454480320000d002e42c039191403950b00c1d062140d01450b5090308c1054000b07000ca180004071001102e810a024280c02e50500d90220003402a81e141522205594110174045456000040c01425608006052100d05000c82c81120200a03481024264010300441021605c0072503120116680850b0388088003020801c07a00c0139102c0e41d070000d090b41400ca420801800119080726000d544100140c4100c00c2644000042c6c0e4040c45d12159048a2010b000200508145100c10240d80c20040c1407a500802c0040c51360039100220412001552290046016420402d20a50152400316446403020b400c4c00d0100b41d004c0e9081505401850784003040d0580c3d00c2c8580e001c55400c030200511411038645420082c007003442c0984c09480c00440d0100015800740c404c1c4940c4010075001003070b004410006540d50203804006603c1c503080014441c6003800c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 745029028 1250 745027778 745027793
    0xc040b03041218081005100512070303030627090302011e0902011103191b0f0c080d030509030f0705030c011805060c0a230c07090b040609060e0a0c0507 67
    0x815071150030781c00c080003501d0800503c2104503803921501200c5100040c00743e0384010504422002010b4800100b41d5034500329911428540d6001603005400384110940f01e24000c108034003581e000362420301503181d4400000b00c80109980c440f01d0b2041100500307000c80e13049904601f82482c0a0310000c40c044403d908820b404000000c2c212000701c0d0344070a81411540c12440110000c2452400f450606c02c20304010b03401c180c0b00034514420404005802d40c8072040b680d1070041c8044d0082552006040350b0300d82100b2940d405d006580c5c4a11070300401e01132640c428003905114030b90140c080e50400380b031480700096940106404607407a0001b0301c02048030741c42c24840c0c942e40445508000d52030100030f01b8503e05011024080e90807001003006a014030300d400240c2120054080404614580d9000040055034010711000501901400c1c8c00040c2c42c223101c2d0086510714004079000c10406507a0b01e03541088801500c20000d00b84409000504003000c0703a80406108030207070a03c0740c903000ca15a0340380c2c0f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 745030278 1250 745029028 745029031
    0x2102090f07202119090b0315011106040303020d0b04050709032006130f0803032a0d020a02070f0504091a04021c0b01063e01061802031f0308120c040b03 67
    0x18520701000c0303018040a094902d031325407624400c1c10520091170800140b0241c0e4840202800001c440d0741004c0240c9910944006510001c0710040e55030b581420314000b00a036000003211080b2904207050021540b0340b501c1a1400740500340c8506e000546150b5842045d1810703806c0c1c41c40c20480c0c01d8003d10640c1c58910045c9441020000701e181c6240c24909000b1044410f0740000c5c060340e0040c4100f2402499581021038200705882d00114906103c183d4400c06101c1c4010401107607002051102c48141c0000d00700d400e070307242d90406081180d101d000344011610b45070700103030500e29200102410a0910001e00f0340060020b01043c0c080c5140980c5889020000b280448107204900010003840d940b058440e4155070356031002d950707804149034811600007040b680189030b41080d80b400581b954007d40c0150b00500d440b80c103200400c2c000d040703644005c0d04104e41041c00042d42c0381c4850181c0d0036840da10010b50743c0c427003c11402c110042441c00030030100107040b44462501040041901c440800146 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 745031528 1250 745030278 745030333
    0x1320070f0204110307050403080702040f09030305060306010e07050406050f0c120406030c2309131503030219030206010605160c030b04021f08010b0a05042102090f0720 74
    0x21200c94940d1040c00101c0b0a1540350549003041441070000c1da5600c00100c50407290800d0b59992034940307034000100100141710705494402d00c0c0001400425400d40c0119103d80703812404c1d2a80b07a0303070741c404e1824500d50031038080300022402c0005010039070150028081490442d0b1840b428960000040b501c3c004070200c5000e8541004201040358a5241c041d290010750103290200181e130361100d000d005600ca14100c03240421021803050080c0c0c680e140183d4406582e52030900c0746820b80320301040340340001e000980060260b0480c21550031240c90f50b500b0060b515170300400d0130f43e20b460000c90300c0d5086a0107241c41160242e106c000072900446400002d18043d00b450f08150501d07104004541c010764242e00304458148464103040d0340c110450f281111212501503030350b452500d40c100e0b01441103802455011800c0285c0d4031310b000c0ba0310030f0b9000c003e100b0313a00b50240303840c0c5000c0d480440001721075031800038003445214050011052100d004200c05d890403030b618082c154494055001c03400d01c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 745032778 1250 745031528 745031543
    0x8370305010e10050d1e02090a0501140405060607020918010e011b0314040b18030c0705090c1303230d0e0a0902160f0206040b070b040b070905132007 66
    0x510400150b402640d4008800080c10b961491828004c15900105184040c060068110b203440340041c2c600301c03201905a0050611071135142041c00c40300101f0007806800d503a1485906200c04a00349441818024000280080d0030f0612036400c010926100500540040707080398140707440c09100340202150112960004145c801008610704505644241d0800070181440034055050381d900c640c098105401c050b0105090b510130712100c0301864550001a0940710008026040030350100e441e00c107030344003120800d4a9444c3c11446940900034200c5c104020003168008000244c43c040c0326881c4c8225040c0c038080e0000d40e40122134280044c2170f880401080c41e00900f04d850345005504a0080d2400300f408504112a9a481e03990f001d403810030040c600b0310302c003064509540e118030a641c01003011504035960350456251200d201a01602d0440b0245446804100c151780245241020b1303950183c19024a003105000c1e16020f804400c0001036000c1d030300390020007400316200080442c1400b8104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 745034028 1250 745032778 745032781
    0x1020f0a03090215031e100f08161202100f210e07050a081b060706061e090207030f121b02030c0f060603120a02031201090b180408370305 61
    0x43c0120141d60300c0400c4690f9030308108000c40d48805244c0500c1404200b0f042150941d2124445144100d1a40140c8155400b060380052103010000b0040400014100c2b55800c40d40e55032083c0c5240c200204000303622824914850b000c0c14850320307a603941c0340c8a510300f1156040c1d0043c050b88220950030220790145882c0e4282c03108260080002c0070044c003040d1503031003180d0703d012040c507200c02880414078052400c01e0443e0038a07544050541e540d884d0411000c008036696108a4004002401e1107642c20f158810f0000032545100e02c00d542c0040d4040d1141c00c0c0560483c6400c407032080320b541e8140501e80e5610040a0700c842c005076000c40d074080300c5e001075070740d61907a141483c5829000e01e00e44125900400400000741c50210701d10300e030724010750211a22000340120682c110f005000407504400010000001c20580c0c0da00302890f2484190f03400124152090750040b1082e200711000b030301d00c7e60108070700c622121154080e0690304071984003900c5003400d205582c0070040380c401040c1002a85440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 745035278 1250 745034028 745034033
    0xb0402030a05060301051305100c11010c03050108100b090708070c0c080c031614060c10141e161103070b010306020c060127020f120702071401090e0103060c0201020f0a0309 76
    0x7054a4011f00132101c5480110860798903965200b0813003081c201240e840e04a21403106016085040d10190300000a228810800c02c0c001d00610092050442a200f4a0080b038030302465481042d95100b0007801d0141385503260002a12880f8014049901b00000e100302003001c21418440c440280038804060242c221f102420140352484106900c0000241e0190070001011031030603856507100141d0300991074880080c8082c0c00c2c0762104a601000d241802e401c00070b010a1401070610610011201d000c1a140c0a503400142d030208030352442c3d401601130b03004540903000c0c0801c1072010403054200c0e40707400700c2542c441014003400ea00803100c0c16000301d80c1164200d420300805c0c5c0506a101256136400750709121b1301c1d0600b0210b5800c00e001950004179480d402c4010b004a0780300582080e9100c0441c00e040310300035502c01c19449210751580f03085141628030341c4101c0307003503049a41d582507400480e400d50b1918401000f07e200c260040d507500704100c9248202e09005040000d4058500007442505c60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 745036528 1250 745035278 745035281
    0xd18150b01050c0f0105010312051c0f140709060207060804080d0b21070e090606031011090d03020c0406090b01020a1401090c030f0524130c081c1101020306010e01050c010b0402030a05060301 84
    0x40d80d1490510105024404049805032f200c000b5030854080041380400c2c145161800809807410b40b4560320965804100c071081d002003402c1d0880e4010350071214400ea0310182218000d0041e030f401016041c0403c038000300741140d5000b55005560082c80840c0103543e5540403000e0b181e0b2803070a40303040d03004290204001110284465031064042c405040365250035400651521a50300740e9192150799034002c000a103031040140c4010000203080505e43d103916040107581d80051191103032007141070210228000e081402034070070031141a001051124800da4480d82c0890131075101c58034541d6030f807501d0000305070382011110081d8002c420030400404503080650801401220103440107040a211400342d46001c50005c0d44200340701c04881d80302e07441303142c8200604c0c1180e010580341d11901c4c0c50134100b900303280241520071050f9203c494440c0c01c101a800d083c0d0204441242c081061880d40d800503500580051811103002000040c40520791000102283c20070340c3c0510025544008201c180e0409 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 745037778 1250 745036528 745036553
    0x30209091f08030307090e180a0b0403030209100302121303020d1209060f0b100306064a0a050405090a080f0d05090c040f330302030109080d18150b01050c0f01050103 73
    0x2203410110703655061230022941e90b80ea801005091001c1280080c090600ca64155090601c000300745441d4070f04850702c01406500700c0300c80707480c80a001e000850300e00f03004d851107e50040e80c150040d00e01e40400e031505503051040142c014071031b140c480001c00005980d5110798040038a003810005180d080740d505110314100c0c10400c540605182c81000c0c02182c0d003004034210034401021500c40f140342c4000d414807080703903202101da018a4078181c0340001c10140e0810608594400d41b400300c4107a42e12810031050700c00c143d440c1501500140405030119100c48000c0c1103915650002d14901810851450100c4004031540348140e0021400490f0381c0c07a1900903c500d09400030014803801d031020b00d0002103c5040703400100800010501c0a1a40c1c1c00c0b201c0c646e00a43c0c0040081101c001a03050040a69120a444500d610314000f0451a03201003182401807850300562044400340040c5000002044000000d40c1409001c2c040381001100401c130010011140400100d221351540c82c240030b04024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 745039028 1250 745037778 745037791
    0x4170d02030103061b09060905190e190e0309090f090c120607030f0c0509010309020301060b0f03090c03030408030f2506020c0d08090307030804020d06090f0b07030209091f08030307090e 82
    0x40300302080000c0f943c070070760507800c0d12012521055800c020007081d0200c90419800100c1c1b032f4202070704010304031028408521900c000d9941c28400702c508418000d13200d00c219106140d002d00c94801140d040086130070a1903020600b01d00f00c035100030400002419940f2401c0c3d4580c020341c807000c100842c0d180d260186101e28040c0340f0302800000720307405019240d40902180c090401d641c4188403000d66070250011001031480d28102c2d40d0700c11111800d0040ce9104443c3e4043c2d80c811141107282c1c606000040b102202d101c1000385050485150b404840e507444002c002190b104c810710040601c0c0310123014440780f107124090040c3e44102c6440180e04111440c0d0703108040c0400d4404200031404d0100131520840d51503d8195040d980703030b00c00940100d40c41040a48841d00c1e0190751380801140058126504d401014125025960040c0480c00e920805d101c0c150064200408540f150802d8507421030034480c11580d00001e10344859001d03285410032500e801c009102c2420802800c030b010b425850b013029 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 745040278 1250 745039028 745039037
    0x302010c030b1c03180b0403020f030303040f080c0c0a17010b03010905070909080c190b0903040506071e02040e03040f08030f030114120f0c1008060904170d02030103061b 75
    0x106400001819000251800d26000074042510f80800d4170072000301c00a078030070680c50f0a040c1e480d207240706001d4205000407801000c020b1046540343c5000401d403403055511660030b0090000d0781c1e882c440305420028501c0014450700111207104d6440c1808003000d0145ca2260850221003540c03040e0940b01c2c100e4506000c0d0349044101d03000300741e000c100001950303900c50000c150403112b403820300d507e0300c1106464811405103403d4100c05c0ca205004c0c480300c06004800d0018503454003200142c8a116a20400d54401010465080002c560700c0c051180c0c1c0440022400c01c0b6416a00031800703444900c046400d0680001900717005500e01ca00c1c81d0b5028201100085003000744034062142c5900c01130150302c00d00c0c09c01c64003101c40c9a6551802100d19583d01040e1615143c00700b03c6540e4620840c2100b91280c8034080c1d0702080740b486081014030600000700442d8950301c41d510361801c010300031403114940f4403041050600354815400154001c6103d040c000510b00c00f9811022040c200d50031790b100401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 745041528 1250 745040278 745040291
    0x507090645050c070c03080a090e01060503061011011802031e100e0703021009080d0c120f140720010e0901091e05010e18030f040605210903070302010c03 68
    0x3041c030101403642030248401d00065a45400070000080d020383c0c18000c01000c0b50542c04810400d6490244c00c0c00078580e01d50040b03e0b501c5600040110409000c0c060018105100054840c0350110807000502c0c111b0416040d0881601c0c2c00310301391a0310707450340300c4808031100040d01181810000030410155400103e180d10340c0c1e60140949480130104180140c586441c0001d000c120140004c0000310360080001402500c0440b02508003083e0f0f114501c001c2c020511501c519502403c420404c095001c0d40d0400d100703841000680d1503c5041c51f0b680304210a0009522401d46408000d001c82c030700812000c0000111011811040c1144403007203070400c60001c0d1103049c20b4a88244c503a0558003541d60110702c00140510a000b24849901241c02c00c9017408000501c04081c3c00c001da0244050864245075585075940943c2da07440741d0882580b540e54108001c124151081026250a02c0042100c44a090318010351544900d1b098a0365481900300190350420181c092203220703e0345400342000d1001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 745042778 1250 745041528 745041629
    0x140d020f0313090e0304050405041a06031b0402030a0b19030b01150c08030901110f0a110a0c14010e0307030b06090a0525110601060f0f0c0b01060c05070906 69
    0x80102910804003e03d4030352001c1c01d0002d1042c8142d501a15015104200c40c1c540383c01d12846500c1c981d904800c0c445140800700d480d40c01c0108248a074541200d103540b48000c180304c107000003035100406410a01d940c56580203525540da020708900000c0c8010b0051130a82181044140d103c1c1c1030f8044001e01e01c0c0580f00010b030f9900300801504507904444910389903510364000c2030140c00018a900c60035100044ca101ca0742c07402c4805031010411542d1130740b4108080300c4038507613507642660b030152032407111030810010344c41070032801102c010040c13600f00307001100100801e1410300c540c0c01c2121052201800c00c240c50504410281d031242e903032130051000f810b0588244010260b02481e250700045141400080309004411101c100140d07002201d14640c0d441000030701a200301260400022182262400610300c2112400300310f0b900482000d0b8103902e0b110060b19417400000c800c0380c2d107020ba00b80024020f00306110b10390045c0076030b55040040041c0780d40b0301c0106518258010080c25409200b8841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 745044028 1250 745042778 745042807
    0x40f06020609120c07030f1b0b03070206060603061c120e06040609150e060309070609080a0834060f0507170601080a18080c060c040501020d0503070c140d020f03 71
    0x382c545140102ca0365070f44013089200d0030104241c201400d50709040d11000f00b0051680e000041c5c41401d00c3c1100c43c0c00342c0302c00c0e40039024403040da0000010b0b44080d000c60441e180c0f0100130742e040a80240b1040040c039001c941031443c00d141d070905980c00e00100c990040581d80142d40380b414040115215817501d0b0070490044c1c1106c440d030040407040996800060f180714003800e1521107042c0c00410322512480e00c00132541da91001409024002403c07c680000c140e80001404549a54000c0c1641d0400001d42c41042c0100c25050402c040c0d8a20a810511107015140307600036510b000365804110b1346000c07490442580d002600f18010084404412050000403c0f4680c1e0802c409192102c00341d2202070101000d8140042040e5a460000c0040b01c00c06c1014001800c1502e00d00b026510555200041e00510380114419240542c02ca8400450194820401160300460342d007413000300c112058407141c5074054412401c18841d84a0305061598540401400b00c1c04841d81004515103007901e6500030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 745045278 1250 745044028 745044043
    0x150a05100e130c021504060f0203011214031314040204030602190215060a03120c0602040f140f0d02010503180102071430091314040c12030801030b0402011112040f06020609 76
    0xa0800038a4000c00c04100803034120200e444a5503102755280d50710340e55051401000d4001c01c40d80d5002103e00000903030808015114103040804640b00030a01d030118145000729144c1e26194010f50801021000850a20143c40c1d040e200109c00a1944810b01000e85002a03404404038041450400c010140e900d884201c020703203500c420155405d12441c0419a60803510740703401068ad5001150203e00002061421012601042c00d0231190070140c50a00c1148900508195082000302a865001d0b502440c001c540010040ca461190f00b5010680242281c015401c00c640040c007820441201c0d80d4101701e03225038840d480101c41c82c24819035000003510308104080c4541a100880c20051545c0d410100c140c001e00d100c8070501c090801d200c02d40400405c02c55003100c3c6900702a402007036100c28124004400c56041d1901c0760385900f903840d45614510000d00880c10440c8144103560034110600400b2030840141c1c0e18240c0311402c202d510248410030307402010840d4001c2c000c2088259000442d0ba = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 745046528 1250 745045278 745045303
    0x6010b0d020c1c0f090b07020f09061519080114030d030506030c18071b0b0a1a06070c060201050c12130206190f0219050303150a05100e130c02 63
    0x580d118001094075003801403000c005080b1511000d00620002d0304030010603180b5201d0383d00d051341705444424045080c040d200b000b0303401c00c0884104071094140510002c0e00b003500240b84902c4c0c1e03d55507050040c030b51302001200344141d0800c0200035001d030308400c0460141203800e904d104803000a10100e5600c0704d80480640415480300c000c648180c0b02408560040c071000760080c00707c4180c14210703100c51038003510200c00040160042a1000113080110450a944802c010016440300c146110190141000e0b0081c0544400070703c052942d5070720010400c00d8495000003610707501d0a140682103420003440001030b502d04000b500304a40400c1b010551003004003107118502411400440c0701da019103c000b54041a40b4046201c100d90000101d5001c1c102035401c40705003a01802c500d142071007106100811542c018804102210b00c10503226075540f502403c80c1c3c03400c5590f03600140b40b455224800c80049090854440c016040840340803041c4031108800b84420802e61800960b1411030300c400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 745047778 1250 745046528 745046531
    0x3020a030c05540f0901030b1f05120607020624010c1e2619030f110a200105010302060412050a0209040b0a0510050a0b0f30070206010b0d 61
    0x542c0c04210611a0301c6070501800074442c1c44030070f04140241c24506000115110b40d80350b46113081c0900e00030300418160f0390300808111050321044c0c01d00c0042e005460f0704036010082028041003541310210b020005240d15402004181011480a424420060f128078803401c449607514400010000c0348010000b000c0c42c0c0780c0e1040b0200d04000400d00140d20490301c444207089001c0c1c050042500e8002203047c583c0f0103948402d0346074807007184140b00700b209607440f0202000e11981418003030703401030b184403805d1400030403101c6c07945507407a885502c02c811342008240c8590f9118107c01d50b00b0191540b612584c0001c0040b94150b0300003c006000d903205010b209031a150903101040030900154150941c050507926560070103180484082c181240d0b0b0150980c9031000040340038680781c814004a420160803040207605003024040b560323001e021101c0843e00c040020244103500354800924258110890507205d014141c820400c80381c0c003404030021540300000601c030300311195048a02d2170090000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 745049028 1250 745047778 745047847
    0x602120a051b010902100813031b0b0f07030c18050420070c06120c0f18031e05011107080a12091a060102011506020c1e060a03020a030c05 61
    0x10031107640c41000070a600030b0714541001c4000a405401c42801580b0071100118a0700200c9400c60308190b048034810b0f4481022109040072070301440031861100040680409581c00c0b8ae151200100010b48440c60400f20483c10401e400782d051203070503240c0019241c10f0b03104004c0c3c50058042040903000703040c071031a43c0d00c11084003203642031314110b000d0014007070454444481e805e048008041ca031080710003081280b40d01b42043c03404e5101d0a440760800d501c881c2c40c500300e140012211050306000c03440440e40c40c3c0c04040007040440e014445034044000d0a945201034034981942511400c03e0036030941c2c07100780881400290700c42d09440350603100d840d00c414044112000c98000e4071070355a024002411440074103545c0c600d9068160303c40c4800b0f80080c40b203ca240ca07400303035541a5604c03403030b00140c12000400314180341181900301d410060884000c640306002e000181c0c41d90100461901207580003c905c0c0486806010f0003001241600742035050040c0300d50050601d21000b9925a140c084212 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 745050278 1250 745049028 745049047
    0xc090d1b080d090e060a08030d0902060c03040305070312080c030a0f09020a093606050910060617070e090604180b07091a250606150507140106060212 66
    0x841401404403070308907070b08070122040241540741c0c075014500d18551140d000401500b40b6003100b20403544610020752030843c0d51810a00140401a01241d128004110034101e0401c2080a48051070145014258913440e5241c54505081890200c0701801800820000401c0300c0ba41074990242d0f03144e9000c1000000180b54000905554000030f40c4075035580c0011036030741d03c154007135501c8036200207401d1444402e0124914004148425240300c80250075100320004442d9085560031829510807103810040c9690b010702919020f401000c0000c42501941c54100880d54400d80c00099038104869014111408140d004900400086c06161034080f40078040d4818800088600e800000c00040e900b03117400e004100018610071134080701000c0d014844400070f203504403010a128048040d40100d11000a9810780303001400c01e0359400e5440b40e0024204c101d00c109162003c24035a1400e0351840580303800e04114070b05a6940321540e03d03055050001a400165032501040c0303160a903031b1102c0304103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 745051528 1250 745050278 745050323
    0x2f04061107030209070e0310090803130305040906030b0633033301030c0e030c12070803030406020a0f030b0906060d0605210601050d0308130804030206070c0503060c090d 75
    0xa920094103c2c004408028020f07900800c044d032800b2048041d6204460100b8008c42990303085c0a01409401d02000032440d81c601d01103000040074403a0801c03608040e03030b9103418012150a42c9c41030b181d03440094204412494550303040b484000705915465125544450000f03140d060705240d01d02a840000302140005c418030b20420031110388a0401c501000030040741d0151b02840302c1110707000c80e051222402e1658001c02e41400101805402459000c0b810300402124650030b4640f1043d40c0120301e00810740c91024401580300f00e000b1107026980d6405000b000702108405030344c00040510304070303840300c1554030101d010744c0045003100c0090300c0f5100301417200e00070000e642c86141c5c018002000e82c02003400d4821103500741202d0300150f8002d0baa0365400d1140040f1900802000195090000742c14902e0204010201c50700823101d2604003a100d901060b0140d02c640c0050b0340c44112850108a903190070041281e001621440c0c10b400c02000c50089000e507041002c0061440b51a984000d2090a85 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 745052778 1250 745051528 745051543
    0x304080306010c050a0f11060a05121008060106080103210804030c020f040903090816180e03040306060b03091006080a06051503150901110918060a0e01092f040611 72
    0x941d42484a03074901b04003280c19007038044502030092000a02946408020350300c410b4001c1e02c801c0d29100c012111b030308180200526104601902e40004140f059041042c0790181015071a0141c1c10b50440c1450800016000302d52440e40074440789803005550700014254005615050049090703410788001604480a00034003600a49004c040300e080c10346c441200411595108199402c40d211640e800f46248440d002d036420001c100a0a40d85110855000005080119054a09064a9690b40c1c1c7c15208640c0c02051040c002205000240f0710600038008041100340c0c0400c0103e04d045603640d1913440a1402400c400d54500c0040e05184c0c02d0b4000803010350004054034281008540652003108043d111014079601c1c2c103078035510040d00c0004841c0c441a0003446440d048036542c6c140008034400404c0960003c1040c1c000298032614100c1480c00f0340030403034000c40d6000300032020300c0d4076030f480424003c00303504080308000c04c04043ca0101c81c1a83c20920705042ca419483c1c4205182c082c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 745054028 1250 745052778 745052783
    0xb030309060921060a0204050405060303070b040f030302070c0b092e030207060608030c0a031d030c060a0201023601020303040c032d03030b0a05060702100806010e180402150f0304080306010c 84
    0x21300420048101c8040d0b005000380d40c02106c0c03c00c06601d406082c159680208000104075070340e19804603000c1505c1268030240603100789030152922003a03a48001d0f42181c240d104002c002e0b00880c0258083ca050300794200700384110200300740080d400e00e080c00110a541101c0c03400789540050400c007840543d4100d60f01504040b02101d0f40c0e010604481a1b5502082e0380580004510380e503808104000d201d011004ca0800034028501c1d24100f00420416611000b45001559400c01011010643c4003060008111007000119440c40e0703640203034089c43c0c080b290880e0441d0000c00401c00083c40101c910020b403a040741000c0c030100003c04130195040380c4416440090b00940064004069064200c00910071098400c0040c060340c0c0d40a1010901071080000e41c418100d200300c0c2d40040c0b054400541c807460514002c00420140c0c008138400e45400280b84810481e0300040100f5030800300e4400104c056040c0e100c900c1c2601010340c51440c0e010103000102212800808100268480c030280c2a0064 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 745055278 1250 745054028 745054033
    0x503030c030406110d0206060906010905040515010807140706090c031e05010b04140f041b060809010b09010344190509060406110a240b030309060921 66
    0x60305885aaa40390064819000055052884c00f01c80c9038001ca401c4100d04c140c0e400500341615941c0411801c40c47c0206813a0412001c2c0d030f000201e076655405454010072814110030b0b440740c10a40014001c940c01401c00701444078800c0d154203408509421264400d0f0403950000e0400950f00d0b000c868943c5591000c1e02010050584002d405c00313002e0504411f0b44680000c104007204c1030240002d60f40d030590500c030b0103101580041e0004283c8813103658810300c64000310852411518980c0702d400029002640010780001c10010510002d03c06c09500041c126040c540c40d40c5141c0e03d9400608030028003420202000140b588402048200022001200e00c5440440e100308800ca40c90b40c3c029440c91141060403d039081c00300c50040702118114600030380003e1605080c01020f4445180940e014040c07849560300810120302c500c5034140640718003031001d03082c2d018019000c070b0030b0700c031b070700e0704440c8a50030070000300380181d480700101c850080068913405040310024a000c0604600e04140310a0760 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 745056528 1250 745055278 745055287
    0xc040f141f0504090f0b010504030308090c040219080f1b130918050c0a06050301270c020d0f02030c1b03010905070902030907060c08070b0c130e06130c020606010e0307050303 77
    0x40307811030007420559130041070800100f02040b80a409a941e58400c240c003090341040f00b8004070b40316030f01c05503100300c8010490b6501420720003c1012a801a081d000b1814116401a00815804140030760841040e0b05515410300f4282d505240000001000b14030400700000c00c010090000d00a4100800c901102006043c29001c8440c0e076007002c20744120381d01e00803540c04086034544440d805040c2c81d082ea0b40c4905680c285041d4442044114403013101414080a000f50320b4020340c0507120764a18581c0c0502101d041150010740b85002c1055600700790741090100b00700750394001800080020200c0c0d0319400e050a001c02203401090750b0080500180500100800c508125400440c0101004000c48000c16900c41013121800802e8400500c10681040340e04041080781007940c1e0403403030321020381e841c1c804000600c080000b031941c404210349000350304206403032400540b45022410155030901060f0700604c0025103031000209642d041c03021900f043c0f0640d0301c04001400240c10050105c0c1d90700c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 745057778 1250 745056528 745056589
    0x1b08180306061f0c0b0c130e0f04290a09060b1e0d32060603030c03070b2220040509300409050109150503030436020a03050c040f14 58
    0x254080b4547c048181d200d40c400148410510302c03281e1040490b80300c521900c0c0c440d59904030080804111003c02600322801003246c604456400d07a000384088480003503402d05521f0040d058070740d03146400344103801c050842d4100c550240c540d190044403c480c000451002803070708541c44407c0b81c003002051503480200d4520303d0041d49103c40e40e4003416044802a947d54002c00d0750760720852902c101d40341c10034040440041c503d2044150031404c0c03040c4c503500413001d10300303030044070f00c01040140c441104c100b269901c000780740c1e014100e19031001d56050040e4548480007070303624005500380c003032a100311107141007002001d90740c0c04138016a92a00070340d44030f6945003400041c080070300451846074078208541403205810301582045500150185042924105410b14404c041e029220103085905101c140160040f900408001d1100342006882d80c0403000c000341100d10080c0080c10340c0e48200320500c11079040000090485400742d000c001801381e01d0000c0342d0490210b103079900e000c000d42c0c0c802100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 745059028 1250 745057778 745057801
    0x7060209130f0905160501140f1219050c280c052a030a0201080c18030d030204080d030b060912160303020c031501180c1b08180306061f0c0b 62
    0x14954002c404460001301720395144040748109220703080c0416041003d1902c480401405064003003c01c84800341080c69000710408d0f0fa42c030491b507600d441000b0306403c0404034606d02c5070030b07000038000300c1c41814000c201c4d010380480503c4e142d581c2d03001c7d14244070310000c2c24420151403c50f140d015040e0780c0803030b034203500112500081c146492180700800f9070495176810005a50201180c05954040c07464448905500d1a40d0101d0303240c40440c2c0c1c0e16031000c052500c1c200100c460101859900580d11850616070b0350801115045180c20135092030003607400e96a60f10140e03056880c0880c4d58141402d0f000c0455490806030f6800703840d00c500080c5002042c0345e0081407103c1c80140580984084a03401c00405e500003809004045040e0310005007d10001d4003640700f00301603100d0f8206181c809010084121002580b458101c0c2c00080014030b151090703290100720201050180c2c001c0c8900e00340b5800140284401c42c0c011700c2c080341d40071800654a0320038560300d1803094000e04140700c14182001c066a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 745060278 1250 745059028 745059041
    0x40e150a06060516062f0703080f190507030204172103130615080109110111030c060c032a040303021b030d3002071101110307060209130f 61
    0xc0905140280004442d4021000c41e030210054080d00000300c0704070b566945c000d090408002c400e0444000e98866450300e10031500c1c4000010a03009600e035402813400a040d048024203002600c07050206101c0440621520541d844d2001100404c4660f5440d004070001d0049500203028a10301009000c80303190045030411034087c60079510106004914000741091101b51100350010400700d01140119220340d105d04401041c0750000031a2a50710190320342502c13a07002054400307201c02e90042240d5a04600c0d1000720700741040185042040d00c00800e038551070010034049008074008005140428000341c465007040c42110204160040d80030035185640090100301d02511600000b0103c1c011000540100e80328020020b01501c010860708035000c910320100003004810304a010815403a40c0040290f288900200c0182c444001d81800001c1158852a286c140440310079900703800d44010046440503900500c2c0507030b440e0890001b02e406a010346440544032403806040741d6a1740300941221 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 745061528 1250 745060278 745060291
    0x2100e06181806130f02040308030a0c08060102060115080a020403020607150b150403060209010c020306090d0810060f080408070516090515060a14070506070504180e070501030b040e15 81
    0x70016403440c5000e100d0850243c820381d44c0008600303600164403000307400c80090300320107030009070402e56241c2d601000c9070810b551000740a601d640301c101e201648042d0303141c0c1c012424802840954504002c4c00c40d80a004c01506040048520005a0030000d6404483c0190750107040e0a540c0c602508240d2042021090220405400e019402e280c520b00710f0a8522100059003030035280519641e0741030300079442103440e0b505200c0001900009031350207000d8240300c0c8a02601400c000e0152240040025a0060945013107445e021024400780381d0000801601c48140c7c20040126150f606184856000b01c007801005449040000d07088200042d000030225000303900107100507140e00001c0d41c2030094540321a500005c0034402d03c82d03090700c9202d10351000b190500c1001c0c6882c0030742c0c960b1410000115043c1001c1000001e04100d460100c2c0318081002400381e1080095003202c0800c151158541d1069604040c0c4a440003045590303030780d00c50b0843d00c200804944012075510400150008c046030072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 745062778 1250 745061528 745061539
    0x72606010f0f051c06061403190f0609031106040318060c02030c22020f120f090a0b0601050c100b150c030409020c01181407140d02100e0618 62
    0x7400700c9000001d4815a409034441841d15030904003480343c005941c46264012500740303820040403859600c14003001c1e01d03e442c02c0e00c61806050051620f007480c00e00c0c1143c06031090020000c04075240038014100300e40e00c0040440c800c0ba490a0440d000c01e000030340f075529802014140020950040904d020b40c00c0c82030840301b4041c1e41d900080c3e4541e54070782e6000c1d4064008107055200c500e4031580f09020b107611850015041e0005a4a06080360003201d802180c0b0140015404003050001d100e09601520f003070300044052814011554445604001c01400c0130740c2c644c04a2804d070f0150060310020700644081321103d400f05070b10140500045800140280c845100c070202060310407003114181107508008515062038140500c0095200380d40b9154555682d04401c0c813070000c0703401c18142490090305103207900080d200819043c11001e5001902d003401070000d400c41902c4ea1051840107d40450706c1c40c803066400941a11040c151489060703001d0800110304101062100d40a0b007818400d680 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 745064028 1250 745062778 745062781
    0x1230702010e0d21050d020c100501050913030c03050d180215032a07020406030b040309090501030f2405100e0a0b24070606120b130206030a020903072606 68
    0x40c03040904409001512410034014000303c800e40c00c00c4610909644da14005251a01c588840c1c0e00321780040c02c0250003600308500030400d52515001d520b014010454600c1c1003810018105284090b4440005050120103402002414060416116080f100c042c0922000b021000e8400c00e000781c01008900c03403100d140300c0c600c1c1345086800362442004c030345082d0030b510303103a0301c0380c01c1c0102c291000a1010090100030300c80040c4c440e0301481c1c00440c8a55020301242c10249800781100030141c22000c1c00a24100c01000403441031106154840e4104252000c00c12445e030440d062101c10408200aa0741040b05018180203800504800c44807503040c264526105e290199007640c1311510840d600010307554400030840c4000c000c1160789801038800c40d150400c02c3ea1204150b514030741c444c031240c120384840b0005111070554140c0d881403451800b4007621050b03030b002882900000e03190700030166003c20380801c6518100400006050b10440003412a08440e040c110313030b025000e240e12180e005290 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 745065278 1250 745064028 745064057
    0x31605010b0415090509060c03130c05120105010e090c0f0114070c06080a142e03050d0201052707090518030d02220e040f0c120302010c020601050f0607020405060123070201 76
    0x21058024852048c3c51450344d1241d481386100c2104081c026a4070848049001400b076551b403420200c9200000c001080c4c5602d005441515107030f00400406c415006101815985e0356045222840d4204c00d0820300c6409500c8407029056018014004054021484000c81c920ba005003000b44074543d400010b0016141c00c1a51004011068940c20002a19803050310912102c803007030f441e62840c842440d1800150f8a4070f03184e29100280400c100035075502d10030710464000d03c1c01e41d5402c0c1900500c18049640c81c2505040d0748201600c80e0388480390b80c0f5008641001d00300c405030350034403a842003100e495403640d401d46030080d80101d82c80e60450b9104088550000307522075080c0200c40d509141e800c001da540c0d07102d0b007240141c1c008041717814588a00b40451400c5803008050070702030080d800020201580c50b2702038038211042c0c128910030351844030000f0565861408845803158155400f14060300d880c40169000010000300002d0903c40900b103003a00441840a07105150003640e0310b08820a480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 745066528 1250 745065278 745065283
    0xf050406110403081b0f16081501030503160212010f23070906080603030d060b190311071e0c0b1c021809070e03190c080609031605010b0415090509 65
    0x144401042c4c80c4061184c015210b00811304043c814651320700b9110091410a0624104000035207408106ca100794000c2c0800c0343d0400000304841c0640114444070350454440503500d0003507441c00f400c6181084116021911001c01316090035440b10001e110301050010b0a0000e491400802141c514000d098807240414500d501c5000c0e10542c0c0f600851582812801c07a20148000c014517090300c000c110184140c9680e1050340001c0004850702a203034105003031780c3d0300000000030514080508000440011500c0c61040b6603580398800501c1500c003840842101c0304025260014026005400c000074025004000900c0345c4585c842603d0084040700f0f403810100d020703124150f100800d801c1991245400c3c08001e090b00840c1c5824205006180100043c0c030300b119016081c0b41d040f2400103c1400c206040007610041d0415101400803460f0a0711029501d010790040d4040d10003035902c0c0302003030203002e50200e110704802800501501005000074010304225105211035146030138005003004102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 745067778 1250 745066528 745066537
    0x70f08100c0807050a0504050a03060603030e01180b09030708030d0c02240105150c061518040b06060703110a080403020a090c080103020f18190c050a2106090f05040611 74
    0x5500c4002c0103859158080f202d64018800c800d00f405070030030010a1513500da00380f6000030751080002190007421450010444249200300d13506008440c001c4881a0741c102c50b10310262100300900d240c6408096000a2800c0019407040b40343c0d0000140c2d03041c4600700358200740d00000c0b031902140e85405846514801d10300c940c1801c2d040003030340480144070a01c4c06803000c0b0b81c0810034043c2c13a400c080c2981c00c4a402c0c05d10644121081070401041031400d42440000d024500010f41a490000c2c03078503880d800c603001c070018039480c0718660010340c0c1c070105070103072000960440c40f0f1401c48150b5851458281d40644c013600050b84100585040064000310360700030480100d280355260007450340707160f007480b0641c45640030342940901d100ea030300802c04188023040c0c0c0c46504403203061141a00ea04030500215025440340320104242040f40100e101d4010403410400c0000c2c1c0b4070700500d0b0340e4911240c002416281c00141c010307810481d580c110203007250080c2c1c0c095400b501003000140c0700094040601d208 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 745069028 1250 745067778 745067801
    0xc080721050705040c0507060c0c032a060507020102040e01120c0e010803160302120a0306030c060207080a0b1312030903030c03050108100203040c091503060e12120414070f0810 78
    0x240d0028046030900341c0002011045d40d040c01800c082040d07a80b4429205201490b00000e210700b8020014913a102e8070b642120005010b050141654104070349070408281d9901605498071000410f002620035411038000707004031405002613503140c900b070039440a05500d00361500c6203844e001145c554081100c5504980c0c54400442c58800001c004456511059500b5810f60040b0040d0081c3c06042d000200078003205540c0000303450b411880d00d038241003055001081150320681c018885800c0015101174150b40000680d8401c0e5140408448441010100180070010506202180f660160030210610744240c90501801034070741d4086048413000d119068040e80300c002d03032a91b003440550045030060700a02c503501d4225140c0c92400c041d41d01590810000102c050020402e0203054071424030240045c00c042c03c0140442001000035014260751112040c07403400220f0100450210a005248440f400340c881f52660b49507a04020110b622031640c241c000e0481d80c0032480c11501c120780c403d41c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 745070278 1250 745069028 745069033
    0x1407060801050f0a090c030b1504060804141f0522020901061d0d080c1006031109090f060a06060306171c0c061a040c2d0c0c08072105 59
    0xb0b20700000c11120b012605210b540144058101240c1240c1034012040c6c043d5a6440110300a0040c906015120169880307000c1e10340e0061009118080d48113100d0b54200381c1011602301348061086849003822512035001803102468180d2000e802c01a400140c8911140501010340c0c40520300c00c0341e00a4507a18009600900c40e07070051000340d00903065412440108403a0b11841d200c040c01007180e412104c07134181e17850318000c902030008100401200c0c0c0c0c5100900c20070301000d4510f95801d09881c03900003e1030301c00d8800c4800109108020040c070007070b2503020ba0440d003070741c1410134035580180036038094000001e080200101d200900103882c922a110280c00a001200300781c40034160005203102c2420070845800407020204505010710046c24000302d007026883c20f4a0130030403045416600c41c034400d100343d100c3c030001c0801981030744d507196911100c1e01d410416000501200d01c0840820001c100e4081c400700450440320005001d402c1e521088074504038641d2200c4440b03410f00700c110000740309031b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 745071528 1250 745070278 745070281
    0xc030e0c13020a0203160f0c1505191101050a060f060f02030d0504020a0e010b0d0501150e040c021e0a1115270d05030d20090d15050702030714070608 66
    0x740040d03008020703041481c4150b90a00010a4040309181524103040c1c40040b04003100b60140a05004a50020603160140103840109800c01402900604c0c10815040c10758103c200d503074500492441144103401c100800292410495000050200740107142005100f42d40c04590140950340b90501e4160356001581130007050382c404000340000400890f080305503d100041ca40e11641c1205018100281509440310a114221003c894059200142c081ca20301d6608054a40000c80740c0300102080e02c000c500b1220301c1006a04d402c08551031410010030100e0981d442c00800704818040611800e1011b0f80440b5403010084e00441c803501100d440d40b0100321500e500c840c5030040c10180c05a94203041c00c140386001c002140c041c0f103080107030b9841e0000640006030301c00f40e104000d03210715500004644180360900440341400b403414a24040c0c0d444a8010040c0003480c0207014a0f021003402c01c0c4518507200d24003e4a0380c00164044030803204032003030303100d00c0d12000c00d07100261880384d5070742c0710315 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 745072778 1250 745071528 745071559
    0x30501050321070512031501020a0201050901110f0d050c0111040e1f08060c09040c090b04060f020a0804060f0207120209150d020d05010e101b050705030f0d0c030e0c 73
    0x1c942c0c05000d2030808900070080200092810702071210000c410700400c40d240d1410901101c40742d110800c0107411504042103460040c1c5e002821703906002d0342881c1c40000c00340c90201041c0b400c207030700a102c0340c14400e0504035032445034045c00600c0881c090354002d00c8a82c0740c4040800c0b0380d00a80c0a00300e800100308002842d03170386d078403003421142c2e01040c0703161600070342e035855482d0070030400b130303074080c0c6001c00005200340181490300030103518448501c0c14411040ca0041c10349294015401800d040001c0d14400c0f8407958400c120441d111908402900d543c0ca0b40c0f082c024060404090001015004004c00002c1d1020400c0e02c00c20440d4000c1c241541070340d40d0080402c1100d920f113400c0d55000c0c011001010150300c42c0d041c055800ea01c100300000f0b103c4812440d440ca000b0071407681c1c2a52900f0f000c0341c9401e000c01c02a03110042c5146003005a12200e16203040c0b4218003407007030003178114903000c522018030810703d03001201d1040164504104400995645030781758028040410f810050030070305c0011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 745074028 1250 745072778 745072813
    0x20124060309020d0f060515030d080703150f0b03160903150203281a03012c07031718060c0a0f06020c0106030b18010203100e06130203010e0405010c0305010503 71
    0x381c80f0720040102d92048142d1391050701c41d003c951000d0359125510010030554041c062040401d080040300180700c2c82692450041040d80010403030802c061302c07952502c2d5000f080000500c0071700754104001000c03613100d441205041d00100c882d9026681140d9035051094050721690b130a481d003050381290202704506a0070003940c00900075262036040103107000c1408070305100c50b00303c41e1002000410b40e00c0c1d0640300341003d498440e12051003a407412507040d41c81080102c042074408800c42a0580c2d0450130000300c0d003003400d01d13400505102d0703000401c1040707203080c0310082c40c00080010008000c80c500d50306001540c000c04d0011280d80d8401c10260340803c4210798040046441440701502d40390040071080e00352441e0f40e2045489410820a10401140040050728801c0f007140085045181007510414507060744c0c841d40c0c080c0d0b6003000100f041c5848108071341e601d00f402450159681d5a4680721010640021a42610503520b031486040040340309008490490b90000c004000d9400c1d0882c8030390 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 745075278 1250 745074028 745074041
    0xb0609190e10020307030e010501090b010c0f140a260a0c060b03010e011b03110f0f0a0215040f1a0f0604020a0c0b0114190e150d0c080c010201240603 66
    0x2115200e4015030b0808070b512400110720410469501088015903070110a080d0741040e046600e5403818051071100303030b0f40d02c4103020342119000ad4181040c240241410441d4604950000b401c03401401c1e40700d0207210181040d0600304015540f001204e0072448441c400e0341c00340703032854000250380c05c80c490080342e0990004445940d00800001d1207651142d030301401c4400d4211881001300290055503151500b503c40d1500800b098480c2c0d030319100070080b031b02007203104032661103e0700c0e10081000300c0400d208100790f5030b5107460100e01010741d0030a800c151020080310401282d01040e20076080d11580490030040e40502404040702c54039840f85020407001c0d422507010401003214203058080403540314a034403402403059500f1540503c0160080c08100702e0b900140002d1607012000803c58000d8103154682c3c003441030010101034141a50001c0c1c0b4006c1c0c400800741240748001d10104000c8030105281031030400c01d0b0020003520703208110054518041421842000304003000c01c0181500a81120 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 745076528 1250 745075278 745075301
    0x80708060c0a0c062c0106050406051503270c0a0506132705011401020d050c0307120509120601060e0a03050c06090415060801080106211115070305070b060919 70
    0x401c4105c01d0303410360240b41801980648055001800300780040c002840794802401041c1d13424441d04c1d00307050224056107040030070141c1c100c00002c0002c0c900031090002e0840003800c2058103401c000c01c84103080d584c0001d50002c51251200700400510340c41d111084a0310640302c0c00c00c600169203000c0f035a1951709203428090f41c2040b201e1102d0450380c2e00d9485040d01038070a1003102250485440c000a190110f0103142c0014000200b05403071800300c000040da00d9441c3d0000170448105004c040c201c3d041e0060011041d000705500004c00541c0802081440c16229956607041990b40303840c003084000d441600c400341803a002940034500c7e50402c2001400e05800180c00402d400c4023010701d00c49604040d5001c00c0019102c6001031007003c4080c01003000401c400c0c034842c21040c0e402460350070352851013400100404580b5491215a8407107a42c20340041814600d411b80300d41560602801d41d0340080710880d25018030303000041991424401c020302035800c0003459007841c10a1780b121001003403280c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 745077778 1250 745076528 745076531
    0x403021531151107050604120b09031309022d0f18120714030d0e010e13050c070b0f07090302061602031906050f010e0a11090301020310080708060c0a0c06 68
    0x460261590300b200c80342c01d80150344551050304010300c1c50341064190307001948950780411007001400b00d28116070304269006403000026071204100c2a24510400c4544444880210000200140d49501071300742e028828150f164134820280744440000340c0300743c00c003084010920260109280c010041d080340700c0c52100111001500b007000510401c40300a88113400d51002c4d00500c0382c80342103400e02c1382c000010f8004003607044181001030704501483c80100e04128841d074081c072081e91021001d003246004910100300e1810400413080c0941d00201096030f48000f10004245c24800e101d400900c101c4196880f00350031801c2d5400c000c1c1a40c4805982d60460120190000250340c0130300038040346117004440729010801c140f0300309042e038800500001c01c400080c00100711480000c100c40b644442e103c0800620b83d845510241928004c64850390380561003c0b042154a662150541060f40d656000700d486941e524100140c6d039620403a04c60b95212424001101042e009240002116100b000c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 745079028 1250 745077778 745077877
    0xf022e06030f0503091e090117150c130f0806010e1f060e0f0105070b0408090105040308032a07030903240e0a030905010207050108180c1504030215 65
    0x40e98400070300c2c8902c058416400004000c40c0c1841d098030304255049501600345a1480784000141146005100d80490004444a20b085070078090008041c40c10f4280d40001c55402c002003211015027081d4030f04040d50100f20804101c030070142d0190703011145084000d090a0b8204190311103a01c1e07024242110700604a0b00151444051507100406000541d4691403070200500800095903090b109050500c4030420a8101080540840781e91203504107881c103950303512940c01210b5500c0b0355172004d0f00c000404424001c28244580d081121181588100306401c4c0441c18540d01c01c0c8200c16004003c240d10f2981080050192001c0d10313881803210044024600740b00480505840d58502210040e400c40700c2080101034011444101410b002e2009240302420200040c0001c5000341000c0722614418011454000c02040403984440c2c01501030034100e1106040441e02e50020301080780b250814606403041d81413080f00b9a064211950b03100d8507200e040740400d07480903020700c101b0a2510250304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 745080278 1250 745079028 745079033
    0x60a020a021e01020901021005150f0312040e040b0f0f0115030603080409050a1505010f080c090409080318030306060a1133061804230d050a0f022e0603 67
    0x2042e81d4010326003000140c0d454403002d0009082001c01c104000e0114642030a114408407050105000c6c2c078001c2d5000c014001038000061710340400c03d0700000000030005004281c440401c1095400345110b01081092a258a042c540c0c1c0c554003201c071410701c9146807004111594400c080410300800a083c00101c4075200e8480710b01d0ba90050308480900e9440300c082c070141c0361080c03040c92071044440f180c0541c0303241000c000802c404c0610000c00d00700000180418a0030001d002150b0b007503840108200145034540c60114006e400071038480c031307034480c50703009209907600040200c0b4400d0300010300035858200410019244000071b41d1980d0440e00c2406a41e268030000c2c9079815828414202d51444038848401c0f040701500c80c003c20710ba000d4881e100440c000d00c03550388001360304150321a03041b007096288882c400600c65169030050001e427081480c013941554011008100314a210341d5000400040b110342680c0e80c8050340c4101c6010806001c0942c02d2907070301ca040c242081026900466140d55a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 745081528 1250 745080278 745080313
    0x2817030106051210380a080601110304030f02220507120b0109081b1c060504021e010f03021308070308120f010303090306020715020a0815060c060a020a02 68
    0x9801140102d03400282c00e002c4041e031100d486500540110ba05501c460400100381100d001c80228114200000340c121500f20280c00300f8070424030031801c81c07142c54918181c801080e44800b0b5450b00e0120b0380403100190305050200031034007900c0d0800800d414003103a5500703214805900d00002c2504941071040ca4005410340e005007402110b0990b10804103800c4548000201c030302030761403103040c008800c00400200c032010038103d817110042103440b1500910729000c0703400861710b076000c1c1c100d52003101c410340201b24080d40858099402a0350741d10300040404450b01c0147c180200041c04030b0400c4007000c010503c031350024081c4a84105036800f045640300300041c9404910f8008840141010070300303004640b0620f40440d0f1182d05040020b40703035451900e01038800b81c2ca50001030a166000a681d40a200c04e20000c00010ba226a50071951b5a0002c100240156800c0c0e403540c20211000e0b4540700c0a103880c1c03007a500c141740003401a01c0e458941c00307000c400a5010342d0b500820b5000300301054418a040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 745082778 1250 745081528 745081531
    0x60e060c100911030d090531020d0501210609081e0702240409090602070803040320010203190f0902150301090b0a0303050405042d0c0206010503281703 67
    0x1a40102c0c0340001c6142881c0f5480e00b0540c00d501070391000346001d400d554400d8032a01107450581d9000700808800c94813007908420030b40390400b01c1c040c41c130741c40702d103624140e008102514205008021598880c0341107404100a04000011070307000540d250702040302507000c1d006c101d2042e4000c914041c1d04462840b02c2c0c04250400c0c2d11541030225400b810360130f1105a0441c03020190011070355080f411a1048807038080d40c001e0084543c2d40ba00283d08002840d0304480c400c6400030410f130f0b101d2400c0d140082c203040f510180c000615400072444032401c0c1c014000e076170140b46184214a0281a14610300f40140303c0000c80000d0f241e2aa2038000c00b50301d5206580e007091014041403030352581440001c05c01c0d00c1c4010403030740c06030307008034070803c00309500c5401c0d1001ea680c00c036004581e1014080e40361f02001d05285403075500740040d1020038004607607580604e220080d20f40a640c1242e0382c81c41010b484862181d02d0001c48252030700114800c41108a1414405100d0f500500404405080603a5140c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 745084028 1250 745082778 745082803
    0xf09170c090a02030f0117120d05071b020102120c01060515031006170103290a020d2f0a02030c0d081008030c0d1d12010204150c050601060e060c 64
    0x200d940141030704008581c1079200034400300661440c10000c400b003c4600c0e05109480e48148489071282101105112003144104d40e48910b948642c0c2d40c001120080400340c8100c4041407018000b00803103068881302402c90b540580151a400550405502d00e540c400c4c42d00e005c035950307558000700b1281c0d9800d03001074440390842c3d801610313482c01101d00004004960071900038400300c200c0c40d203102c0395111809030540380c0c0124011600d134490032561020203c0341d100344c0d500391103070b6040020011007540500004000c144081c00503009400b0340304140400200740e01140d90b601c100030b070f50554110b0018038099803184101c03454031001e00c44c82c80c141044110035a0001d840301c8144089140542c000d00050486007010b5441c00005030403403a501c0e02d505130040d060104180240000041aa8004000702c2002d4100c403464210681158001d51050145002c9032015040780c0c0d484c0d030710031080d00307400b1035008009103500e90130124141c44c526a611000f41d8408810000000383c40b60a0003102903081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 745085278 1250 745084028 745084033
    0xf0507090509090c0d0809120606090c0f07140a020d20041b0f0207050d0302010204090e06010b1e04091b020c010f0e01030e10050405060f160f0f0917 66
    0x104044014a50082a07200c03a225031020300502c8021140030030040b00c06242110301c50843d41c1c152901d0340181c041d440c0c5a960203009801210451030003c922248514001ca5114450b42d4900124030040d00902d85001d142207014040d0038001007010403031100072302c045400c850303502155900081c5030b1a01807008458041e420048100325039011030003100000c50407039080c0010b4405002403030000ca000060383c400c0060600c43d050020740280b29a001900c0c01800342e4a01c3c80407800c020b4080e5001d4440c100241d460280c590320038070400b24489040c0c0b50a02130341d6152001050300c0300b04880c604540403001c1d4408200c00110701589104415210381c06400400700507020721006401c2c00715540006050010400041044650150f2900107003032007400c0016801c1c14a400789840c28426005450207140303048244420301c240094454840d00031020060315a949a42100d00d030851000c0c00480803802c4e1100c0180e543e8092070350b81424480615019203031030b580d2400082425501842d540454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 745086528 1250 745085278 745085281
    0x5060903070311030406080619050406170c040902010c032303040c031b0311041112040302150702120f0313020a0e011d0c040504020a0225050109060c050d0f02010b040f05 75
    0x341e00b061200740d0200092000d117050034075108000d44048001004c0724800d1030094135004000b2103401189001d444068070801805444540c0403a048001902c07142d001c0c0f04402003074a0925041c080c00d00580d07410382d038440710000342c5d650607103a821405400040405408000803054200c14028520071800b40f0038011800d40746080400207160316942e50146a1444030060000c1606881038900310b010580d40041e10044904041d480750203030500e8103941c2001502404141940018408040841d1603a00c1031552a4400140c0c2e5030000c5a80c800c04146c0c0030722400c241c020070000a5030b4494940010306154030351603400200d0300711054012160101e2200014000c840341c1c1d040b140c80c0041e480a40c12004e0a06645c5050140602d2288130300c01da40006010407007520900c9400d5800c0c041c0800c10541b43c80300f0310380281d0f58045010701400a030400200140e010b10841d02090204c0e003000c045c142c0980542d00488084040c06505d00c10f541d00c5040425040d16107200c0c0340640709041000141c079 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 745087778 1250 745086528 745086533
    0x6020c030d14190509071503020403020d0b0402040605120a030305100b0a09080f070303320c06061f0804060b060c101d0a0201050f1c1802010f050a140904090506090307 74
    0x902c3c44a0565500e160302c0c2508000420030001824801c0d0761a9509000041944000c110040d2095400003034001070010003c07130170441d0398951503000e64401c50b81481134645440a100700603000100250580d070005c0044000700f8042c4d844a070300b21031940d00214010762103080c41001c6521401041c2e0004d0580801080300560610049081076124800b92000610f19200180482c003258284100103050306403811500596010344062014900400d40c4c841d1100242c540c4c841904803803080c020881903960311110002c400c12a80c0d4003215840b100040c0d02c0e280c0300e5000815500201c80e400410070040e4508070306007040070b420b03242c0f0010302c04a28251a520107040c020040ca94160040d80801481c000503a000415a6074815460140c6034172514040b18100e00d10400d851544036440c981a02002100110050601030500030f0300d518007600e20400c0210748600c03038400800005a081a03000103a118028014900c00c13400030004540100151201c0341001d0040e521210b8590000a01404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 745089028 1250 745087778 745087801
    0x406060e040e06060307030201050c0102190906020f0c1c0321150e1003080d020706060303080105010314090613051c26091504080d05070503060f030f070306020c030d14 74
    0x80c42d201e5000f070202070410741e000c40e44d100c0690100a042c01001300e0820503200c42507050b2252107050700203031034007110311000141072005580520001070040100740c40300c00100003a61010030300c010b08600c00b100c9c9200a18408002480e60031010040f4100e000060401d0000a85404040144000078003032030010380e00a96044580c404401d9010344010000c00070416000d1078102c039000195142e0394941880040020f00c0f03180401010309190880100a0650200609044c0c131001e0300e04102c81140c140292403038000c11115480c2a03031200002075082a9403002c000c00c10761160080350003004e504541c0f408142108500007001032491001403442c0c01c0359a0703c6842d1805440c031750b841641080b04445890384102401c0b2401d1032070f00300218003045181011160000d500300b00400c030900300054010a550300540d4614411505100c940320b2034030b00868070242c1c2d00030000090243c10b280d03035900e0000c0d40200c3c0e00c00109010900c00705010010901410520341300482c150005841c0c41e110801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 745090278 1250 745089028 745089041
    0x1c110c010206130305090a0b04030609030305090307240212130303060501170402041d030c0f06010503010e070306050604200403030f0e0306040308040c0f0e0610020f06010e0907050406060e04 84
    0x2411507200744207108000c0c1d0409503e40701c1c00d40524080784d03504000300129401d04001e03403000b141d85100080020034048964041c0516034801c2d070303003800241c991094003580c074091003e0180081002080e00007810020440c0c15642a00f940342c0981801c52100f0760204079030b0101c0e4091460082e103407640d010141d240c07040d48050482400c2c255070390f00c59007496030294900100001e0240b07580c3d4100746103581d202400b503082c603150035040b80d0740d81da0071010b00c9440304070074a003004503441600d00201380d07844d040c05021030004411000b030060703070725644441002c2c0c500070380003035085507590504405e0206186120007840e8404200b803640c880c82d514004043d4040f0300750440400006a8032a101590040b40d000e27086605880d26a2054403075007481c0210038503541c000500540f034544002421590000b0b480d1117100d0465540080001c400400c0c2c0e210301c40031b08021800d402c002d005215812101020310307000700c0300008580b4100e4591010604a0304290800004104c0c250200e556600e0640900c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 745091528 1250 745090278 745090303
    0x801060b0a08011401120f14010f05010f051b011112013023010c020f0a050c0919180209090c09150f031b0102150105060d0e1c11 57
    0x40c0c030307201c20741c1c5009140003018000c810141c00c00400085080c1c1c8500c4c2c2030004055015020000c80640a900754020704d0100c1000c6502c5244400010300000c0050100c0b0407110180c440c100c28542d0810102ea04d075000d1712040102d19080e21001912100034410820200c005404c459510552403a40d52a0100164095400d07680107048600d4000300d880b41c2c0a60101003a00e40802d1140f203454107441a05022542080110380c140c07449003a500f054000200d803101d03e400b500c80b14048003420703540310010104050499030141005120038140104485d40c48011141c45070150201c1110310416600a603401401000c5400e02070003d6203002c1c50019003010a40c4010300b001ea0301040400d07a5064010141d00410f0319060003000a81c035000b036076454610004003170780c42402000c03440e10381a41c3c100c40907900606c214041201d0750140502c3c4541642c000901542c105804100800041c28049048078106e009100e801000d203081160400d01c00707041070303d42260251000c450a0300d00021038218 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 745092778 1250 745091528 745091549
    0x70e010e16020709020c0a060510090e060c04060c0503120115141e09010e09040c03060b090106080103083016090f14030703020a03120201050f070806090406150f080106 74
    0x2075084590005010821140c0003100985c079001c25140e204d003000541280500801d062004101600300c00e211308805486403040108025010b401420340e4401c0202c07400d400d40c603003c1105001c668010650245020300c02d00440303140c122204e0250246160030383c0503003000e0784001d0110305000d4000511139002c5250494a9043c0720403440348aa490312901980300c8541e80c00101c500a41e40b18182c0e64410f404090134040c0141854036014103030f0103441c0301c203036040751070004609480c1c0350881c0d0081c100c41f0326a46d4043e503a400d58541c403a01e50310402220002c0c20f5101c0c0074005c1c00d10031422407503607804138107401c00403880d00c18845454103c800301ca000c100460b805007030103504c049400950940d10611010665480140d01191606e452608083e42c05100800000100b0011a2406003103105503030084c891911006007141e601213043c0d6200d0040b415082c0000c170306081c41d10400f64071600030003000c07404d0f20b0680c0a101c002602a00030f85200310b0f88034401d0007016001d0183c00e0080040c0d000c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 745094028 1250 745092778 745092811
    0x1707150c0b180c041a0a06090317030c13080a0209060402041503020d090503030f011806030f060e010914151b07031b0c061d040e1e070305070e010e 65
    0x80d649000c59000701110282e0181c2c58040000d042d0402c004849144094020003024140c40410943e80c2d4074100e815104500b6141c020a420380b28498800490b42d009450b0026001c180015440383c0e0001400380b5882d000038403c016500900c55030300301c01408410b014211003002c0740140540d462004010074050383c01000200203a580480c07442112081914006807a402d1058410f00548400440a880c41c4400b0003800308a400d0760b46d2150496403105c0914440302c443c031031b0100c19500948409400c180b1080c41c514041003c5400114800f44104000900c50f4003a40e1050b5202c0388a10415020b81d10500040b1114504c02e0074040d0022200c5214980503050a160301082e4031800c0c40050410100360b183c15030010018a2000d285503000034450303034064a4400041080710b4880100042d1640b1031040034203418544030b040d148100c910007503d8085c0c52140f51810f0303e440200000e43c01e1040402c00000b1980c00d03c0300b08045c110150b800c184039407505454a80c2018040c1c10303451400d0007003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 745095278 1250 745094028 745094033
    0x4050c0306072003040e0108060105031009030801060e0111010501030311151303140c01060806061e131107051203090715051207140a1701081506090c041707150c 71
    0x307440c5010242e00c01028640325410f0180da4114065980010061031701200003040030440803900f40e0582e001078003140d40d0728588103020404c2e070b11201c0c00580450340c004014002d183c8244140d42001d074040c10021011001f9201d0319013100c209a20a0b40010001d81080c0d81d450340920141951008026030340c0c00d0f60603d02244002002c0801c401014030190344c0520080076200c1007502d1079004108000c00428ae5603412039a00c82130102c4045100310000f6040c016280c21401d003407452488068070f80c1105041c521036000007401c0c0e46448030b800070424000c07403000401c100101050084031407030341501c906212500d10315100351500300341d0b850411011040d008561290075101e8000f0300c507030300c1c00d0191514001902c106544845006120500045000c481504022a100c0c0711f040c03800c2e101c845070f82e18241e10340c80d086005101c141041a03400031440d02e1a00c0c000311500011404001482c2581d01c2c5213104681e07840c0c200d00780721500310003820013205081d4011541c4042c0380b41400040e4105c2e96 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 745096528 1250 745095278 745095287
    0x5010905030303012102030a060506030c0108070f0e010909020d0b09010f061d06040f062d0c0f0203190c0906291602030d03020c0f0d1e0c06060b0304050c030607 71
    0x140103d0004450b07003c9520817003451071540d0b90049401800b6140091090309100c070240008545490007481090154403055104000c2240314005582e01d1480704000010201c075803080301701a007030420400f07080202d2040308505c020b1403500d2500320009038415030b081c01d200007440160700c8461071080c1910108013168004c00403a0400050180010903c000400020707500d02482d0000814031162040104481c2c2c3c004405c5001c003240c00b46181a100c1d0311040140c6034a44119200000602003440c81c1c00080019600b034900d644010150384101070403000a100c01418010141c8089034102420030008280e03102d95806400703940b00410f00382031521441210103288400c1c0f14030034180080ca08080614549581203003070b80c0107041c0c07484140340c3e400040280d00910000c000c540190307070542c59000030015080e001c00c10b860301c0328400b00d051b071000003080407021600354041c88010545c41000400c00d205d0785c0702a00302d426100303459040074109a0702d030060588200d4001c0d80040203214083e50030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 745097778 1250 745096528 745096531
    0x5030a020901120314030a05010302040b030c0f01180e090303070f0206040f08030a0b0405090d171302060703050d0f0f14040f02040b010207090f06031b0e0c1312050d080105010905030303 82
    0x1540f00a403065a054901124501c910442d09150707010080240840c1040a800040c126030003200c003400b2030814007040589070456103445503405400d20f48580065400350032540003404c0da0070890030800b55503002992086108035506185a0400820440c80540000b030110284450340b001b41030038a801e940d08280c4400014018244220100015440194580205982c040c0c054828030203800d1020300c550740c490040154034042000c00e03170680041078a0b003803d144208566261660115295001c0c480c3e5030303201440540030001e08100c540041601030203065000c801c286000281d4000c8403418000312124032481c060160102d10a0001042a4500d42ca0741c454045500003144081d22005078030700170302940b140d140f403030520a9242210400342d01a004503030003002e505900f0500b0303200072082510b03d4060122500382d201e000c14030003410100a85003402074440000304240d03c1d0f409240740340e46240d2048405611401d04120017650101c0d8081c01400c2c2820a8002a4100000039449000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 745099028 1250 745097778 745097789
    0x1c0603030816230702040903080103150e0303130501090f110307060504060e040b0307180902031902010c031107050603010b0c0c0a050a030816081c110901090311180c0a030605030a020901 82
    0xf085195148003102800407144000d07070081c820032001c0c02070300e400342c0120002d2006440e1001b01080480c0100700a008902140a030700c00558075554600141c101003400c2c032982a40c8542d40c403290440003980640c1401501406856030807400c4009408141c81c0c20525040f2034200103051208000d00394000444148664080381c0114007416a0404240303810304d03e5000c103c0d50a6107a60142c040c2d4059848102801d00940c00d80d0540c0f207025108015812203030000a00081100500e80302007480b0346490340c000300895003920511680e032000605203400a800030400070100190001000f4810880380043d40c40581d80080d800d4a05000941c2d400a20321000e00203003c0000c0c4005c00a800200e0075284661003080b05440b070b40c1902803841d1652020020081e460703e8000071440c541c04a40c29520140e40503955909480e0542d40c400c10150060b5036900c1d0080092400d00b10440c5100310b2942c407454048201079200d0f04405002400c4d142c4643c003441c0203400005404001d40c851103101d0341500d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 745100278 1250 745099028 745099067
    0x11a0a0b030403020a120c1109270715120b0103050403020601181509060602060703020304020a050d030203120708091e06040b070203070c0b0703030b0f241c0603030816 74
    0x203640e410245e04050030307402d00910f041c4c5201e82c80f10301c4681001c01025441d0003000320148000400d400d0080500090390348649034041504903a241e103070381c096800301241440050b504125500c0170901c1c20b040d0301070030311800728444801e0a401b0500601c0789240aa4092905201c5810151030294a44406001d20105280d540c1c54400c165041e54010790018404026049283c669401d0362030b006040d603004000044c00f0303080100754064481d00075640070310340040c900da1869103032904008054003204001c50541c001448140305041c03c802c0010b10a01707507512620510b15142d401d090034010020750308402c2c070b0325108803204c242d180011050390003580718411040ca511158401d1745180505040185040b1701c80b02c0200d2404598406807107500d100c0e40342406001407080c100107910118520464009074404010380c1030790844401481c4046030317884441e1600324040482d0003807a80100c4220105520b83c1001c10030540d0152409074003090f00980c0c865003030070481b0000c210b01039400304a10500c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 745101528 1250 745100278 745100281
    0x503010e151f090f0e0f09120910140a090503163f030c11040b010e010f03060f03051c020a0803040f0804090204061808160315022208011a0a0b03 64
    0x1030142e20f0b200c000e042d10902c0c00000c0c03907503810925110b54007140c89070b001442d40d0012405140d00000d03c19a401080245242041c011b0024414942d030103c180c10104103c1c103d048445194103c0240809240d9568400142c0d080c94145460071078444104007044c008642e08112141080191402c900e00d840b031000256402c01680300b12040c0b6110702030010890300d042e00002c06800a982203071301480341c1800841c08042c0c804000803507041580f8180480c024462024042d071080c0d01ca503088500d541030004070180c591006030210001c40c4c0040b10685c0c4960150043c0592072100f500d0307800c5040c0f00070102c0c1034140d40c0319076260101410080181c0d080131141401c000c0c0103026a4094040d43d130f411511155a44001404c0b00c41000740350221603c0301101090713400c070101c0d0404500304003148150100d0718542da40c1e10a94481c20400300c0890b03091201c0006c0c86000d20b4400b400c0c000c2c4168649042d800c0c001101c2c01c5038140c1c8034181003114543c030040b10544440a00380d04030764400c40e005459 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 745102778 1250 745101528 745101589
    0x304020307170607020708070303050d0e1c05220303140d060518010302010816020717030c010e0a0209010915030b04050c0a1e060503010f0b16050a030503010e15 71
    0x1c1684540284030001c084907050501e50314005140c501c102900c0e403c4420141d0b0b2080181d0300d441c0e2a00024000843c200590756514800e6040500005079110440d07ca000d8401184402074540d00040b0001074400070700d111000f061b08210480c25502c10900b083c4c081d00d07668000d000010105000070540102061002145195901c08002008050001c3d80c42d041d042e0519052524240800c90100f41000041120084c00c5140d192040e1a550024940c003818200840c0c9290600804004e41f440200314491200c0800e005002d00304004000800b440d618a20400074000016040100c8aa180811040f0310100250310f00741100d4111080303800c152a203007021410681c444140c10b40002003044001070138030501c40d0542036840b003100c0070901c068591000b00c649210078420403e5090061806200c805143d40082c026180d0b1040ca003035103044980d580c2030520001c980203070041740e008070040000a00103100c0c607610856512a280c80408401e001600034a07100807459120030100303594141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 745104028 1250 745102778 745102783
    0x2b0806030604061d1204090c0302030f06060c0f1f0b060a020a110f18040c0504020c0a1101020a120e150408100c0e2d010206072a060507080601030e0309060a0503040203 74
    0x10218011410b40d540a117064040f210306921920078011920300e819400480a8800d00c2604e014035100c0022030246c1d250030080225680060384400300c071340030b58500350354040d104000310b05081a00324a07150b0702042043d0360740112030f01a00100d020744804c122100b080340c1c1c04105171a8042e4041d00032040500641c0225805685450906030071000c2400362641260034405424403d07840780c030036108050740b104184016800307171301d00100c500d07407061141c80c002941e55102e1031040d000610440740c4003103064492644031650500e100001c111421051881e60401034a4010808121100c3d2460545411215940ca41c2c840f841032071599580c1c400555500d102d24004d1036000e000611b28842c100907444840c0078400454090041c2d03401c400040c0215500224403184554680d440300c0100c41c01e000079025082e007056240000c4010740400d1080002d03281e2003494000c1c0219520310301e9902d0900e0002d411980c2c10890305c1c2e001d074802d002008041c0e0b07070b00301100d000c09094a0043d8403074680d44082807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 745105278 1250 745104028 745104071
    0xa05040c05060711030708190206071e14151b0306040f061401030b090609130503071e031106041502091314041b0b0a050a0c052b080603060406 63
    0x140d01040000f000c100303001d660400101c00902c00c4054034020742d13544c00816640c3e4030f420f50701589044002c8200740940b42801c017815289000c0d030801f41c03092582c07525103246994a0b05045072155403448251040351010030801c648a071004040300c041d403c040c0d42d0300a0030013018030145900b030b45c0003001034010345581c1c10081c413400c1c10310342c02e0042c140c9824162514410003030109000030703c1c00c01030500b103107440c81c10b140c000c100240211340301e80c8440d002002c14203600001a05c80d44810849c550000e0f40484540440291101100c081d070a082e19005040758a000e0f200320b00c940c4a4403e000100d1034240c04400d84c624149401030365040c1c0100496039540c0209100400305180c250146028a40110894820fa10548102c4100720f02c1c2e40b503c0010b03501c60701401e445041c05210310020343d13015000400e800c1fa91030070490218070640e0754880c82d01d520344000900c0608480700030550000e07200c40f202690052410700c88094545600400d82d1148000d0014003529203174082c0d1300700e1254440e07101c17 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 745106528 1250 745105278 745105289
    0xb1302030a0f05010203090c0607020d03032f130506070b15120a060c03150f030f0602070807320c1c0b0109050105030c040e0d120608030a080a06090908030a05040c 72
    0x59490b80301414194000d40088644101c10700800c060288180f41140440c3c002690080100c10114040c3c0c07022802840c90b00d05040341500311400b51003104080d004030702c1050b40c0440301c0703030b50b40d00810741072540c070010561020740540d1062006000082144008903404048815603003209010840094035113483d16a4108440c0500a01d040c184022900002c4100f500c0751018819000040c0d210001002c2610919840d2540d40b00244002803807400c00990b50342c007500000d800c0000a4841c40b2403644101c40c02c460f0702465000f141000c2c021001c007200799400800c01c0c42c1050090b0742d4070586441c0c555104a01c40c407a00441850b040e500400b80c1a480c917009607428075150303121140e1000520007030040d144240b0071894031084601d000e02440600c00c00000c041c0100e0081d040c4240c54401c0c414202112542e1243e0011405400400c09000038503000d5841c4141402e0905808013203e1142c0c104c552001c0c18180c00c4004190b039001200e4010300c05660000e806e55984c100b40104082503000f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 745107778 1250 745106528 745106543
    0x10306060801180b030c2e0206010510110c060d020904110c100216060617061006050f0c0c03061501121107080a0c02090106110d0f09050d020a080703060608190b1302030a 75
    0x7e01603018a40154280d00b0706801e075480107011040f80c030583c0d458400741b00e00d41d030190410941030b103454800c0d4000d01c5e01c1492074007101e00c040100000100107800c140040b142040e40410f0807001d51816026403500c441086680342d24141405000c00d071a9a1641030541100740c00080c89407144120b0079905100640185007002520f45030401546a43c4007074071401420f200e11804034032510310403a4032000f154050b03201c941c1703042c41d00b411549503500b00d00f0100402d80510307400450310f500d0511015105245e80074894200c9400a0300142c0041c81c100102040c4038600312a52061424000849081b25000a0500d4030b40e401c9640c01c4810031360410000b5082031150000060150300304c041000b4043d4010b0546039001e401207812507038101c4140c4240002442c800e001c0000382019052042210700180c41c2d89a0030780c8640038689003486a038800c4aa071a91080d0812a0090a00c102c00d040e410103414400700e02c002d42c41c0c00f00303049805032070355101410f0074000004660f0204601074407560310258 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 745109028 1250 745107778 745107799
    0xf0b1803042304150e15030a020907170117010c020304032a150c0b0c090d080d060305120c0f06010f0501030f0e2e0b011b1e0f02010306060801180b030c 67
    0x1502e00400940c032500061034045004a00c50680061031841c11b5900030340205088541c98003040411000940080203000309001c0843c011940082101e020f8030780d2409030b0b40543d1042c00f04c0790840c5d6800180c0c0c011904180000d0000600a45203a1040c41141105040b108010b4a4840400d045036100700780425400c6482100c0c56044086d0328001802103000381e155035145691034203144160743c029580480d510316600006031510001c1c00c2031029111001a0b013544a5442c03510300682c001c00620408000714030480c8100c020809c040c00c80040d00d01800c042d5140c0000040d558a0f10b000b00c0d8181030b11602564403060340c03a804036100f420b004040f220312242c41e0201c0846c201c40c0e070000085000a00081d01c1001d03260340520b108288043e5241342c4d05103543c22a0498410b01020101d0790080300c124000200c60f500c00d51108450b0150040710b540f126188005411961507610207001d20104400400540c003101d10b01c0d503404407803031402007075600c11040001d041c01400b5800310f5100d00c0002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 745110278 1250 745109028 745109051
    0x20f0a080105090106210e030d09050c1201060312030f09020d061a1002030d090c150203031f0e062e0c0209130831030f0b1803042304 59
    0x3400c05040711015500802c1d035903200d02d401c80d00b20400502034041d040c50600c880310049134660003406035660203010340f81404004101e201c184c848801c800c0d62198030031010001203140c03e0000c000c400900c1e4008000d07492941d51801030740180c80107100141592103c079620503460076040007040a60090030030811220f64508207004040e1642e641030f4171241c03150003803914209000c0c4084041c4507034004505061600f4050405041c071820203d4aa05000d08001101000317404111502070054000c1d6860786080907002013005640c0400e4280d011041c1d07400c101007441c83c0320150300460283d0304d002901c1103c07003c076410340c001c9111a81e401c0d00c40490b2106210b510011520629208840c0b20f1200c0e00d0300102200380034000300c40500403500412230b0160240e0807601031083c800420804818500c91104c0c00c4546900c0c40c0d000b9a40d281c0061000c07400c014090350700c0d69003e000004201d41d4111702d02d5240750740e401903004050081c542000f004500c071001d078505103c03904c802003003404142e0b03c13807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 745111528 1250 745110278 745110287
    0x60108130b04120f0207081009030e0418140109021c0201021c0509100201021201091508060c07020a092c0309090901060302010e151215030a0303150623090103020f0a 73
    0x200d07011400513460505a0385024400b1640703a00301c070441401000e40d03052140e004001403090150840038424002940343d480c0e00c035802411035041981d5400d0b0002040c03414403001304e5034294807802079a40341c142c0c0000144d5034619560b5030000342d400b52111800312440142c1c60088d4600001c044200030082d12050300f50300c00001c1c02944400d03074200c2c80900b40ca4809900782e02501d03296001e01001880140b0506429a00003c2e4410724651403001c080d954200c00c50404c1c500369001d02c21a0710020b14030040d8105042c840001b0b1400341f4080006144000840c8040b03000340b24441040205500e000c42c0b04241002076580c840c0e001032400807a1b0038807840c0c05c1d0080c082ea10049002c14020f0b84400c85514284503403800e09004e09201926018050080d8540404000d01d100d1407a00c4440c50300c1c040d40c07001c0020702c40842c842d44000903001280d40c0070002c02d0015a005804101070301c0c0c1400c9405113042d038215404d0000c1c1c11119102c182c1034006074040d001c0c281c040c051355840403420f8041309070712 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 745112778 1250 745111528 745111553
    0x160606030201260129030705040e130b041202010e1b040f1103130303060e0a14010905010b162108070e0f061207180b0903070b090306060108130b04 65
    0x3d88800c06031030f004402040e40c01d5080f64400e001c01600c5401040b00860121860180d451903800c9002d550701c085d01100e41710f0b041582d00c0800588049400c1c820241d4031681c1d113401c1000c8149900384032985030344910381c0340c50090000340024458415020207600075081410011a201c00761000103825801d20342c1d182c0070300c50b03039540b10386c0c2049a034081144c03207882402c10b00e07408442c4d0f04d442c0da034070b003d41c0317111100c14101e0450130940e9448000401c0e040c40d9405c54080e1428036804100103080d090300054044040c0c222082003441d000041200800b00c0b4100d401800004d140e4000301d030701505088132020700308c46840e11424032401d10640d10319408807240b0701c1031400d274442c501141c00e41d0003405113003110b002c5e12680000d020004403081e8035950368182c2d405059850811040c894082c81c040d880c2d4000e9104c1c1c0c40c41d15002c03032603248034a818061a0040c000c032000c86401c001c251400030f41d4a200103001c09050105040100f042d00a440b00d06000154200b000c8003402d0070540f5268114048 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 745114028 1250 745112778 745112783
    0x6300622062d0c03051f290307030b01030e0622050f100203060a09050115030f021c0f27023003182d040f060806090c0a03051c030216060603 62
    0x84d210000f00080b45070601d4400c0c2183d0a643c0100042c03d080784500c620a20740d00c44004240d500014a05040540700154071034603080d2b8000c10002e840c08000b401b41c0b444a10201e44540002041064010300c2d842800300c058000d000810041041d8181582098040d1524a2050003440e8034802c05031001d400070350050354107945800a55542e18000c03400c440c02800b030005c20011080410154034441e800c01c00a040c10383c6001464003502d8103003030a002040c01078042000ba00c48822070103401081c481d80c007c1d646c0310203100c0d4a640803160441c0c5401c0d06114028495866510354075100025010980c3ca030181c01c00d9440c4e011011905140c6d543d805c02c180e40c5d10203121214903800e142c00c1641c0120001040840480d00c195000440d0000744018171041c40e4019590b003000da035003400640100d100410350302d00a4141402c008644508203040110600d0081c0488d490810001c0c400190420403010702100b0304001c0c64400c2e904034080d00c074100c69030000c8100c0c44201001c2c416984e0025040780d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 745115278 1250 745114028 745114031
    0x301020309032802030d110405040509210a0206041b0f09060e0106050909070c051f061e030206160809090c1b0d1706300622062d0c03 59
    0x58460f020841d044154250400043c0c005110389212140d15801040701e000d1441c400604098852022600b00c5004460840380b0782e00c40b00ca2006000c8460b115440000311103682940351101c1d090029640e2080a4401040340b8070404104c2d04610010001801510400c0e480d00c10403907440012101400d45d5015116007448008000100c190103801250036040014080c10180e999440c001e0720314004a110544090042c4048403099098584e10040c2c80780c000303a070014905090100020301031800011600310020011018405a5640b400351040c00e4418203814071294903501d080600c60054012454104480b202401589014000074281d1240c3c40d0305000c4a60191592951340d41d000980c107080401c030003181050196105c86e45240d41f00201400c4180101102098080352000c05254210322560400e40110804801c3c812039030095002c043d0406080f070900849071400303001c0c220080c01c19658050504880d1603046481c6202e80e24440510000707102e42045a020b8461819401c4c0001e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 745116528 1250 745115278 745115317
    0x3040302070f060e010e04090b2d010e04020d240209040b0a0b090f0a120b01051203121602010f0606030c020d0306031505130615060905060a0f05031005030102030903 73
    0x36240c20512a080b03c44a585584080707041ea0010344280005441d12074119440e00312200120f041040e085014490034107441541108070390a01003000c4680e04034604640608004000107036005106681068045500d032460b07002c5482d0202c510304050003c000284000c40840c3c1e8444a030340c2c0503028500c0e09917000c0c00107008520030003851140724001c1060010092081c0801030911451640c07002c200078100c54000364071440184950594070400712207000c850401482103040c005000c2c202c00040c400114100324104044081380c11004140d42c40b064034072200301480b20b100b508481400d48610308100800e94443c50f004000d02011210740f005031041c0c408900b08944a8460582141e821100441c44400e050340c41101a08000d000c6680b84c90340c046000d000314a5603c20040c600700c024010380425443c107100a850b9007210b0b400584944014030920400542285e0442010300142c03410070f03030320358592016001085031600241d0301584080304010314080000020450415921607450700c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 745117778 1250 745116528 745116539
    0x12080109020316030c05040305031209010b150d0c300b030703170f071704060323060d02060c01020c0f010f1e0b0a0513050a0c030501121b0e0702030304030207 70
    0xe91100ba20340100050120114030485446a4050b991800d60352a1440c982662178627090701c1c641044204800ca10400d506008054a0910500e46101401d40d49079001000b20340c1001810b006000c2d40950b040c0c2c484081421b4148076410801d2205404070540f603c01e00991403544044081614014401c3d18040e40038109142c0020307841d0031298084c8084035195149050715025070450314003109140014440c10001075461102c4108280c0d40f039241a84803460944020240d4010780340da00c203541310b100070982d120800c25030010740c0190140d941030130103c01403000ca9840e21a03500341c203619500c0400c45d010071100c08140c504000c001c3c20028000841d181949508450507020090308401391044058194802d0360000321025000030402a54150303a02c002c0f4500d25210840386680958a00c00c000c2e2588140c070522000c21500d01d0104015810a10302c10300400b504440500f0031508195500c151045485025026000310310490b003040c144880b0103940c039003040c0c83c2140940039400c1c000c1207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 745119028 1250 745117778 745117781
    0x204050915181b07060e060106210b06070b070e090a0c0810080717030c100903120911010c110d0b0105011b0c0b030916080309010908010e0307120c0f12080109 70
    0x28031801d440f100034581c005890280650150301d08451082d04d03611448280c003030500c80140280b00319150003914640007902c403290000040301c540300d00391800b4802050303620b4500c141c40750700e41d00c9002c204140e152941d00742c802c6062890004c0d0f00102ca9003c0203481c0107103800003080501c6503200c0e5465038071006001c099503030540c0201001c95108500c200a060350b0107a402110300e55003003ea03481c1400340c03241031303040200b4054102c1249403603140031410141c0c0031110008080400380200f01030b100c96592411107160060100d41048140081c85091240f100d4500c1000720b4010102903d04180d4545007110a0003441600c4c0820500c941406030000055507111405038002044004581000c0c2a400e080c2c101034104411445034018602c018850b011041d406004070200840d00e88500c1d000040401c0f02642040712580d05103001204940d5001050303509031680042001038084808104640136040c040f0003034601005103000a007840245015482150510340d40d5904a0f80c0b00d100000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 745120278 1250 745119028 745119031
    0xf0b0603060f150a02070f0b09132309070303110d09091a1003050105040b04020c06010504090201030207021f02150105180723090a1202150d020405091518 68
    0x540040081000826518041c004075004010060800f03405070000603400700700e90070101c07088000d6800210240300800800034154024240f2007015440c01c031000300170461940c41c480707031a090280c80d24191820942c0c190080510b101d041804040541b40940c141540d94107144015408503926890755048004c001c00e0400100f1881c3d01c070302a00300e1411000e54028103002e078042c0d41d00004040f0940c1c40e075880c034100141003003840c0c2d00400c0035414803041100326104000170620440c030411500100001c00b00f00a4111501110001001003c03800141c001e80304503880203611650f00c400c40c4052030015140c4141f00700d0b0355802c0350846800d220014099000a01a90340d000741e942001d510518007004440f64412458541a501d070700c1a501031000c0b5144217448003d4450000c180c025090812117696001840900c0204411a1483d00481c075000301c041c031401040b54002035054540c00c0c66404a40c0180070107011034a49181c000c01c2018481d1030b140c40b04d8410140e4003001404248d0310724009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 745121528 1250 745120278 745120301
    0x6020c0a0507142b03020a020913030e03060702120903190803040c1a07081e0a02250f0612090b040303051e042d0507032102030c03030604022203030e040f 68
    0x40d409004d19180e001203090300c60404400310300c03e0200e1880141c4810703419601079a440030180c3c900440a140c0944404032080e0618041d80c080703010001c800303600080501c0fa00d46071042c075640d1100140007081c00c042010121040c019410b18064080024038402180b003580100d01c0307030003400c1d00d800a04031107407076120740800225020700201300841c504c0d800810b41d4500d61825003030b68500c0311b0300c0c001c108c1d00b101100b0009030308400106522a0340c5c0c0c4003c0600b0314001c042c40042c032814191030341710302c0c90140a08420003054410310b01d0004c249074824142940c00070742590301864580340040c09041704079a4084803c403019a100031030112494541d00942e804100100400704a0b003c051540d50a00d00341942c0e02115400900400c40a1000501860180c6080c541d203508a4086550205003800c44404540c0104841072050001105980c1c100d07104403030140e5200c41d5140f10040d900301d0000f855600d80e14000d000000c041d003041440a0f1408242c506002c070602e20004181202c1c0802e000c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 745122778 1250 745121528 745121569
    0x402010203090f04150801020301061b080a3f0c02010b010f1202120901020a080702030304030e061b060910110a021f1d01050f01050f1c06020c0a050714 67
    0x1240720724a0310a900c04501880138000290a8030f0b42c41d6040340750501d42e4405407850358008010b120381035011400b03d03804403081c40c04074402880e9540740d00e598810503c0340010440b4407181c0d100c18041074031080001038440d1031109035900c02c1b01010b2030041d130540590303c1c0b124544514a022030f070040c0a03031380c00c0b080305840d500d01105194809441510108480050582e804c02524035150905001c40303010b80b100400060304c4004240000c0c200c2907000d084401554814010400003940c0056070020040083e00d0590300c07050003441c0c14030f0341c0215462452003030056800300300c203e440010300c8100450408000340f0002268000340221480388100100040e041662425010340304109100ca92035078031980080c0c00088c070f003405000024046002d00322070f51140e09014074080c0f540d2500c2c0c0500300c101e61002184d2501d5000502070100e0b80d170020918400e00d0403180910031943c0c156000202401c0c15078203610306902c0c01c00d40312980c0b409246c000484003e6481503d08000c041440d101000105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 745124028 1250 745122778 745122787
    0xa0512070512060f130515070210090302030c150f0a020f0d24150e0108130803010b0720062a120d140f01031511040306050f0906090309060901091d160201050402010203 74
    0x11f002188440c002c0c0302d441584262085c075500248244151080d486c0280c0c051926082c00908160130921800072050f6000c92180030300c40205580c41040360445054880140d4451a01d0f50707503a29030090310740f012246072030002d070030800900c0b0703010010207641c504e41e503a42c10035210750041059117841d640b01400242d2001d603807601c07940a10401c2e6040400c1c107031561890340740c5641301d0216078401d030008076070004046507950412008000107891980350000079008008418007242e00c9014180000c03407010341c02141180112584403a5a107440002000d1b200602070092502c500c41d0311944c030566210f4541841c1c40c0b041400488000d0240340a00740e0368903182d1864941c50b0141d02581035401d440b0b5a01d800d01090903011000520041d031040e080440c092504051011422200805e00703d2030350000010003200712804401c44483d03140882c1c4035902d03000c50f040100c51100254000311420004204007000f542c84854402d44100c002d11020600038040701c20803402d80d9002c0c0c03402405a0b01c01e00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 745125278 1250 745124028 745124053
    0x60806071103090f010207030210020d080c0a080c030705160b18030c0a0308060a090507031a0f0d0b0c1c0e0f070e190e0102220f050a0512070512060f1305 68
    0x1813212026031030500c11900315607100d03000603a4446442c455040568405010700210b5604510107642c880038140300c0c541000d0400f4006850740100402c000040311000001401c030324068400d85c0d80781d8071354005840741007046281442e01c100c1700fa90400c01c1000c900340c00c01d0068030004101c84854034040080c1100c0000d6a4095610410107444123038445180348000c103a00480f4415588510055600400d0200e06007001c00444140e031840c0d14010b41c00c00350944d016891300c4598031845980310b24290354076500e904c400302440c05004403174008040c03a410b40780030a6080341c210003030450034801903070010000b0003590703540c032120340c0328403a09603800c82e00240212004c05a41030b0202c04007600462000d0790b120300542240d104020380d85100b054468214103e00d100e2500303101524100c666864410b0078400000d1905005102d0315109582080480100d140e040c0524402010050301012111242080c0e080c3c484a007240c1d24042840210f0000354400080d28003014a43e4001000c0e028404d00341 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 745126528 1250 745125278 745125289
    0x120c20190b120604140403020a0c1203051911010207050a021509090a09050a020a0b0d05070f200307020a240503040f03030f090b09210301050a23090a06080607110309 73
    0x1442e0b26070155417000f908070045503103c1880c1c402ea1103a80504410b420a14010380c03000482d4001d142c00d41c042034002c4c00000c2c4c1003c1120042c082c45a00200c0b120f0803000100d0791b0340d8002d00b00841d554000f050320030821030001a00fa07141ca00c2181c41a40c10360303c003011b44259000d071483c42c41d4400c40d01c8010030000c1403194003040b0514001e400f55084001541c020071241c0140d50f01c421101c1c00005501040d040040c405e0542202c0300340380c44070000000c0c0d08018031404500301800391882a0003000c0030031140400440314581c1d400b07031201004aa50b40b0361421800c00e46a001e002c0304210140481c840d51107602141d1060350300400c035032500c81843d14220002e05150603121005a40c0b181e048001c5203460150303e100e4040d240c001c2080740d4103a8261940e00c4002d04095440c00302c02d00040c4103e42d5a0b008d910706440501114550740c4004414219407500c000e620b15410220120501665000540100341601e100e4003c59282c0d4603030100c115003441ca2464102d06540090104c0151440c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 745127778 1250 745126528 745126531
    0x60a02160f08070f0b0a0b010801031110090819052103070311070c09020a0e0d0f12050d05040c150e0108190b03010216020a060f080103120c20190b12 66
    0x10b000510306121043d41c507080381904610080e01c0d030401c4c1c103040241005640c001c0c514281d8003864401400e51440e580d25200c1000302c3c1d40c1c20301c01e1001255a040301c41c0b0a600002c0100003410441c7c01142e4900b6050409000c500c405945030300884100c0903440ca030041c2d0704070301c1907140c1e101140f45039a5900210000c200c50301200701816400c210303220109041c40c104d00302400da400c1e0010b03510b182ca030401902c2452070001041c01039184030004008100280a50015142c005080d194280c0005104543c6031150480180006145c0f000740801d00c203110700148180c816525544100b4440000290340040030340705001d00164001c00054800803040300c4004041400345000316400540000007030a90704101c14010303034502e0f442c00e01c07020340c0340c5980400001c1c05a400c2200c116a45024000c0c1203580500024240008615148414601c1070140608032904404120b05010b401004406006201d000440c0300700d180000405103071004003014001c4440d0002442c2c600b40a0180c608e405100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 745129028 1250 745127778 745127783
    0x6061503011e03060e010605041518050903131205060f130f05120409151706131703040b18010b03030a1101060b03100e1501090620120408060a02160f 66
    0x2c080c040080007480380c1c003894502c0e840100c0003182e040d04000503c012035144da40c995094848400d020400d10200d01020034042c8484100030031702e41d8882c0501881c3d131281d01000001914084800030704502c03400020500e0502c81c1054500a468603508030510030000d03606090b20103c554019000a0603075082007610511980070b40d110100000c0c48100c040c2c000c0c0c3d010b01c0e1160b40700e00241100317104101c0e401c4080c2c42042c0441c070819418161311550303200c0003400441d8160b80d190055080c001002c0c200403900a0110314565281f9045c54000305220040d10401c0303412540401c503002001040c0644414590050021800e201d00f4020840d0914002c44202260355610000850029451002140300c3d020441d02c015002d840c1844059070b4410042405010000c00d110203451b507a40a803000c02266039900d800408030210703040c05611f203514401400c0c0588a01207501d41200100790240c0300310b50119066807100d6503a425805c0980c8201c13400c506800450705c2360200000c00850305d4415950 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 745130278 1250 745129028 745129079
    0x6040b0a17120a0f260a06170703080a050c010612030c050c0a030b13080d0e0a14010b01120207111f1805060a181d0402090604090506160c0b0f07020606150301 70
    0x24a12010551780e080d07400200d02a201c10003805030703038540c040700d1011500d0300b0001e004031031031030b141d80c0c440d8041e0000f564208078001906540301c4030300b5080800500403119200000e650f0614020b00944000c08040b41c1c44d020304020000e461805816110880340c2003c140e008564500481c440e4100030ba2404880024040c021b000928002d40701e50501a80564000c0440c14040d05189682172802d42c08000309078103000c038600741664481e10048018050400158458480d8540700b0343c0c00c0c42410b400342d00300a00390341d05041c1c0c100740c2d0b46040201c40b240e180c1765075400c036860101700b01300140e003d1f40f07400c004100490020603100f0a80e80710404c1c9020107040c4050b03100d007403403a40b45241500c14145042c1d100305000079850402105504868103c40c100700415690380d4071505e500c4010000b482c1050080c44c0886618000d00c074120005a00201c0d4404c686003000f284944a80156403003801445801d0003d8498101811501034000d107031507005056a10f8465007180700166501456500d9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 745131528 1250 745130278 745130327
    0x20102070b04150509031306030c2c1203040806151f020102030a0b0d02100309080f04091401090b1e1305151f051206040b0a17120a0f 59
    0x80c040d40700440c015840307659421031101d440d90051080e94805410a54a608108881c21101003490f01030003c8a003c0c2c20b02040304c2c090384109448071040c000040910000d0862f0300c250940c40e800ca60741e48103600b01c0301c410b0050702c0c2c184e80b01e44d20700032800f81b00500c0d0b00040c0800e0310103200d091481400e84004140085640c0303155482d116043e0b40310603200260f900441480a01d205900884005800c1544c08504410a070b80000c0e4041e00e441d80b030182490b54986408040c4105032040b02d4030315600d0740d0020340d655540c03820301006143d01606510f4000700600045842d041d80c0c0100c000c88000101840d10b0b0850307080148114840f5400401d921284001184c07401c2805030180500c22041c9208594400000c40c06120000d070000b0184040f802000c0c01340c460740d98002040e034807096500046802c040d40c4100108004040610100d80c2c0601e1401000503000900c4845c43d0800800310300303072010aa00c080c00c0c00700b1405481c1c0e03071901281e01031801000040c401c2c060496854442030310500300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 745132778 1250 745131528 745131533
    0xf0904021c18050d030902010c0b04170f1305090f0115090909140f15010b1e0706051e0402030604060209040216030801050f06040f0e06060d060801050a050c03060102070e060102010207 81
    0x4980c00c01d4204450200c2200c00c0da81400340a01c6011010b04d41410180700d048440e50001701018100240142942540300c04501030048005070b03011000d020360507071075541a610241164a2700103581e1030703080095424000c100b500b801d02400d0700403d00804060700b940d00300a911141c0030f6401d0151810070001c6c4100090f4401c09000744151140950700c802c0c0004d240307140160900320b00d590307441c2440e80700d00c0ca84100c80490b0702030607046806030300003261103601d681645549000711702095844482c010400308240455907001e01e00469020300d2a48995417401c04000180c24101d0b00070750726401110011300441d4031600144407060008200610380f10650340501c4072170030785a41c1a80020703050801072000703042003000345002140458904c1d00700351900003c20181c4000340619081c821105010500940350001a5503a010244500303102094a408540740200800c030382c3c1440c06400d02001c07504d1501c50004607801000d040e4081c2035030a003011016109410b010f400c00e41199420400d0501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 745134028 1250 745132778 745132781
    0xa18050303010308130b03070c0b060d020d080d200703050307031404060507020606191401230a031a182208030604050906010602060f0703140108210f0904021c 70
    0x2851041111946502403600c4d0881010442d0300840081c0001f0818450026080030003038101d01c1d401444110107a0b2520302003440e41c0e151807002900301440164030001c0256103030161001d03d525440400c160850f800c000c6050319100c01124044180800c40a00428410b00082d035108180c0e05000c603910110483c5d245e1140c04c00c4074162801561002030082d8a6410b125080d0082d42c1159442030300c4840304070130504540c1d43c0c4280c03141900301241c02035199001d06007600b0340000300c010910a0034402c51400d401684000c1d01140001d140031280150010b10b040350421168001e01040203442c0500d001014071180680204000000003e580107900f400300c0c0a41d0f0b4051023400e1058403030400701e0034401030754400361220045801800050003000e500107110343d480008601c2c24011503c4003182036004001e64804c81e0b0100203030200110701901b001844542c100c845c2e240740042c8406003091814036004d5800020003501042060500c24079240d0090501203007074801c501d582c840b5a955180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 745135278 1250 745134028 745134031
    0x1204030512040f0303050609010f05040e0f010c09030302060c2b0605040e3307050711090a0603121d041524090f03020a09020318010e060115030e060a18050303 70
    0x114048264403c640402d035050140c1c079000b40c41a1540107540d414005102c2e940e0480b401124040d5640c0e03040c1c141050810882c1e41d02c0c1426000c02000b010040030401001c4c2d40003804117a02600c60000842e001d04203c10403940b441c06031244651116103071280040c0c0000003d40921259500c3e02804a07d5640740d04c1a104044040d0005080d400c004800010f481c03541800300480e0002d5242c46440132265401c0b805c1e5102019107001c981d54081481c280c0c0e207040191711881e0304406c10508004010100b54001c1040c0c0307001d18401001706d840301800b182c08140c00c101b1070340c8902c0700e043c03c10303030b141070a41005100150748400180003a4565034007008072241070070032880c09000205410910b42c1c20100303602c0540014595604114115004526154081d12403180d00725800000150510090700e07206054890184c0203000100340401850340d01c0400f0b00494050380036a42e01c14101900911030141003a00410140142c0c1d40c4841441c6c0081081d40480b5550384800c0386003e000230414002035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 745136528 1250 745135278 745135283
    0xf150906060e0603250c0c08010614031b040510080111090120030702010e0414070e1005042444040f11060409110322020105120403051204 61
    0x31110301d050402011031800081042c081d84003041404400603500a14142162281c1d0f40c0c68074900744c10030100e0340c09115100c050035014002c1c101280c44541900020201c402610308904042ca100c0d0405443d504190381d80004050098081d0301d640c100743e00a02e5024035104910600ad903a80c440ca1406d5a00000c2001a026000518000c1940e084610008000c4000320088880c10b007500640b9680d2054020190610001c1042c843c000d607129003003050310b0640c803401903030141020030000e171107032008810341d500c6821010200c082c510b1080d0f003500d00b101c2e4001480340380c6006501400600250802100040080b00c2c1005403040041107200d08801c00c00011003500c031095848058194040c95184e80f861003410010300002c0340710000e4402140380c1164070842641d0901c1f0001e0b445126a030b008501050400c0500d540c0341108002852040301c0440c05600000681c003003c41d524100d51030000e011520a00420561225007000103901521a040140c0b4086c04500036100c1101d088408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 745137778 1250 745136528 745136531
    0x1020a08040c08060c0403031101090c090f05010504020c0a060207320d03090305030708070c0c0612050a020a0219080c121909060504050105130902130510080603100f1509 75
    0x303000c20082c8650180d8010050040940900c0c144409003c4a9100b04c1c8000340820440b200007111185007076000310541a44140c0043c541690b0301d45900107005182070707900da11031505000013403e050078000c55540441080c00f40a41c0d040a82c0c3d03044c000e410446c000d8840d010501055a070031183c4401c00450011500041c501d80c0c0d4090b0400c03803030244000811010981420b003254001307900001902d802208604003070015a85001c004c80f14072002c884040c0000300c0e00d010000340150044d6042c01d0a441c4046d041c81a99194007141003684100940c800c0141e01c914000d01482e1020804100c0f664800c0d45924a0802d551885524143c0ba500d80c0071146800052800c51440030040411001300c140d05000c80d44510340362001c1c0c41d40c012031180c2d6042c000001100d0608a15207841c210292107954005c42d1107200d1042c800001000314080d450040400000c1c00c40103078010302a003803041c0401001440c0d1182c20313074005c0000c1d080b10310b12000b00d5501c4050580c41101414451806464a00300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 745139028 1250 745137778 745137781
    0x3030b0a0902040f0602011505090c1318150302090106030c1701140f030d08160c061e0612080301030f0c0302090703091b0303050d0921030915060e0402130e01020a08 73
    0x80c5101c42d01ea440d170101040da8074181490444d604160040c0f011241c04071440c903003d0ba18524500b5581c441e200c00103e160a0070000401c02c51890740e00001d800101000400c1844110850340e41d01c24418003019501c080844010441d6034800e0f048200d00c0103d40c80d0820020840c44012083c0303560030307008408000d090903060402418040b9242da95118114020b01940c0208803001c0c0c161039002d00000c41041d4508101071003d0300074000400b80c241d020400700b000503400200b9641e458114800c1014450a180002a9040c48008000c040d2030700441c61a156920710340c1c40d003100003440c50040720b072501c0844000016980b581c0d00503202d400e0549000c91002d0701883d00c0782c4100e0002000c200d11a4030428103002003030f440700644520220074100080c0c0a25641030001e07801000421005040d038101c0788501ca0b032075150b00816846407095600020b1860746d580040c1c00e4902c14040c80384541c41c0800000c0141c900041461141e440709400003130780090070103c40342a80c0c016000d02c00460704440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 745140278 1250 745139028 745139039
    0x50a060f17010f0216020d0201110a0f0209010501090608070f09033305091b0a0503010903050a030501140d02010e120d110606060406020d18080319020c09090309010c03030b0a090204 80
    0x148070b0f001a154042180b915507510781403061041c0802c00070f400750300901c1400e070459011b0785442c1d801d08060401c4842c906141d141090821740080000c901440c50b61000185550144a01c802a680640c076000b285980c0d1002c2110b5550039040504104820920004085410341d400d82e00380480080059814076801c0c410714040c0c000210510303250030310f00002c1110400b0049407440c00d0925520340e4501c99854440055181465134100135072551902c05513008058006004146541c00c81d101405660390b80c070309d44016004448159a00120090f00000040d80704402440842c0300040010f0140c00c034a114291800020403145000b05144806040c134505007000071660150040b20034520381420304500940f141c0409140030140911482c201030f0301c85100b81c000c0b0181c40004201c076254040b08400c2c0c140240e421181102601400242c0405030820701d506504c6100d0b503200540c50000c2060044420344c007a04030540426640b80c01902c115900e8520840080c4500c80001d40c6a50512 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 745141528 1250 745140278 745140281
    0x17070b0f071d0609010c060213080f070501020d0f02100507051c0203040503070f0c03080a02011e0902030c01110106210b10030b0a180503070b01030507060203040315050a060f1701 79
    0x2a194200344900b0002551001010034403800d8500d40c19940f0b00d0b01c1e00002801039035000c2c90b00d48010304070380c004140e400b4286615031101080303600000c1102c5800e07042e440d02d980c64111394002c003401038004102d4854458011403182c03c0c04080c80c41190705e10171810302881c0c102d502c07e403845400650b001400d590700c0b07000b0042001c0c56039140c1c4021861400c085d519540d482c407c2d940700910100c4c1001110041c450229562801180c1086070165240c0d200b101c0240202601d00e404040c45802482d059541d06040c812800c0321035000d030052810003403500055400c0ac00d180036009440d900c90340701090303002c242000e440040c0400c0910789a05440713446c0552010b01c0042140600340d0704004104085900e1508954102c2c0074403d0028178058801c140100c440c00002000d00f05110000e05c5808101d506000301c2d040701d00880588050781e484040898070b174032851001422040110001225010965103c0c58001c14105000600030396a08e0303407940c0d082060b0f4065005a20360392914038050800f03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 745142778 1250 745141528 745141531
    0x4050105040327140114160204110a1b11040c0c0c08153103080f0c0a051b0109020d08070501050702070f361a0301020703020a0b0417070b0f 62
    0x400d00030880f800c180d5041c1200c00218414640b100c5030380031145000780d02510381448030702c0ca04800c1940d500b401924070050035181c1c041c103c1c0521f150800161030303401550181ea001400c29901d402d0361014403030001c03407824105201955118413030800c280040e5182c1c440d044c0703000569115800c00041505001500c8100b90b440300c0142e8024040010240c07844800c801d902c581d001111541401c000d0740cc00e111440d50200e07050320446065210030a2580102480e0302c124001944010340750764507108030865000780b41c424808942d0034004e00b0034071490000d4002d143e84000b40005001031940d0000340785103482c0001622101c0b0006450018450280221756000f5200c0c0020528145040b2070300b162003665206565101e03009800010103c482e00c500c03883c02d40070850ad803407851040d60144000900039840300070b8000c0c3e0040071200590030103009888138540c040d00649640d0046494420940d0002002150041407503405232107032506240c09044200d001c4c0640d0341302c6240103000100744a40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 745143884 1106 745142778 745142807
    0x601110f07060e2d0d0f020411220e0109090501201312020a0909020a0842011502010b041b02010b1c0605060f09040501050403 56
    0x1d0010488900c883c08803400c07011341d5001c1071a56018007040d01c0400f50f040e69540b0f801d00c20b181c90040b0040540c0118000340f80038240c1d0b400a4111401e031240030f41d0031130300071480e40f000401c400781992180d00c800702d8a17000705080441803a1601c80511807050100c0d203814440307041003000c1d0454a881c4906540e0f00d04c0c80d5500b01700310840350f0080911900c006070107640028409a4141c80c0780c00c5180c01911010b446801e094511000e4401400d099801c0041d1200024150b40104580086040b0364030040c8400001042400c51750012120001d600254013403070048845010303443c0380d0468100c036614503281c0c1280300d81a40907000b09a03d40e076200780340c0034055400b4884280c111560012540c0204480e11101c03042002c00c02088145244100301041400c0000b081684155040240100307403d20b840719800001c0c154000c00c99041380c059441c1d0081c4000c00d038100100754081e80d07 = true := by decide +kernel

theorem cover : BRFrame.Cov 744964028 745143884 := by
  have h0 := BRFrame.cov_init 744964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 744964028 ≤ n) (h2 : n < 745143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
