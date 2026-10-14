-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:13.432986+00:00
-- url     : https://prove2.me/submissions/14e951db-9adc-49c5-aace-835af127a553

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 547661870 ≤ n < 547841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 547663120 1250 547661870 547661893
    0x605120d050301091512060519050f070309032007050306010e04050715030912020c01030e16030f08070b0f040501060603060b0a050a0905061303050106050f0f0d0c1a0a0305060102010b03 82
    0x5400071500c60516000c0c5c148820b54400b0000c0740000b103424100e6110b0b40b11404c1082ca40303008100401c000340c180e04107112134600380c0507000d01a000100503400307040d6075542d424180742c49458070107584103c15076090100e10660710700703907602d140600c1400d100344510000032580c0040120110b00407036100004000050a0032607602c1030103400b1002d00c00301944d035035100300442c0c52083c5031000c880058029000a6446900040940d018541040c5043d8040f000144600810032241c07401c582d040050100d824105140c144580c1c0325040024110800d00814800c1d14003030013140c41d004a100d04000c10005c0c0d6282401e409440b0180318404c1e07007150a11034040094000d00040140004514000359110f071541e0010310160444120404060030215040c41000824480d00018050448100801005500000b50404221400329004641e00b21061040102c048012805414990207044011001c905c814a240e007002e40420000707802c10002c5801540184115800100007074050035508a69 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 547664370 1250 547663120 547663139
    0x7021f0603020406091505010f0e130516090503370302030307020f010c080105060c011b080105040e030414012d08040b070315030b15060d0e0f240c0c0a060605120d050301 75
    0x421100100b442b20181e40b805195413010039000002c480f4200010312803d00712239191308a06007107106424001b9510301404181d0f00007860701c01d05c603465900104035004501d016a5000c400441844160304120b0b003140425801001843c4202c01aa080f04d05940950071103600340da07404400f05000c240000d0041c00142020801800100000d00011654041540d920006a010344107110300164a0500500035858070707016023510544194021803c1601705a0f0a490384402c04c540d42e0b0510111000b84098404020302c0d40c07065001d001d601036052010b00b40042c0c403c40c0116000c56a0f00140d0f400250914003070300c00c81110500ca2211550341c2411a0b90720001d84002421010200c520b800c150241580c40c40010700e1002251900418410800c44401386059101252004142c001c0c6070381402e0704c00b103180300144ca1020101d0b012035036261401d4061a61246c801058001c0c003506500030140500c1d40c1141040350419190078400c034189500290301c440c81510300b00006601003004001443c507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 547665620 1250 547664370 547664387
    0x605070302070f0c0f06050703080a020a0306030b010902070c0510080f09101503120e030a0303150902042606090d08060f06030f0f01050102011a0907021f060302040609150501 77
    0x8260400510b00380311500d0b64900c1903c1d0000c1200c10081041d4203001d00030044c1c0c1004010b000343d0401300d040c00c405603800b07000200c006250b10401603000c1040c401a520a0708048021600104d0b60107580d40c4940038200a5489201700344c0d9080010003002400381807410b16890008003580c1c0710011070f00c0d41e603450300310204060040700d001d21441d14250091a914820402c824440c40d1102080710701e11f03c2d0038800d0b1410301100800b03002c80e06020303541c5a18080340c0008011b81c03501c0c00050b501d0402c2811803104d1001d411502d0399a00c040f80105003800f0b030303030b111051201042d107011071010768001400e80d5400e402c64501a0982000f00403d290601070840e95400060080c01c03620030103000e0010500e1038004854401c1e80c01c4410091148020940b115030380508401e20091022151841c80640f01c80300146500380030b01818000a030001e4403d0000103031015243c3e881111400c0c022600c4c1c80a04400c0c04182c0c4030310714000c400180c031b0945200385e1101075100e03002c28007120700c1e200040d1089003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 547666870 1250 547665620 547665631
    0x801030201051c0509150f07090b0307020322090b09061507020d080d24060f1d0405090c030c09101a040803070803010312080402011211090a03080a0f0801120605 71
    0x150560f080d02c450ba060207000e105a070650004c0c40c000001040c070b6003504401030b1001034403000d45401c0c002c5031030344152000b0980f180f104405a0329124240224a0b611030040030300c00d5810b21014078003071124030314107400446010907414024100410300300041d0400a0b0f41c034944c00090390f0655442c00311001c02610881b0b00091150034841d03641d80781e10b407107540200c60071100180d840190300703242090102c220320104140584015603d0500310064480b01030310030341000f400121701c154002900c070004140300440700500180300314106251441c0d96919100c000500ca805003101107001814070b038064030b1041550b2202c0320031040c5030040b11a00c2c01402c01075070300503450400010540e16003c20045c01c215208991907682d961443c106261499000b0401e03404100c1000144009130b80d00641d80c0e075208810305000140b110001c010005075214a8a0564100021800c0041440600b00113003184003215101c03001f410340d0110303080390200001d00913548030b01c01b140c4a410219455901c01503002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 547668120 1250 547666870 547666897
    0x1002150c130905011d01140d11030d0c050129040c03180f021507021003050612070b0c0105010602070312110304030c1202041a030c09090703080309030a021c080103020105 75
    0x101c1c0c0c2210098100c8840e800c00c210a0b074603600100406414032a42607420201c030401540594105885c0002c044558000d11380300e8100101c3c0681800042045403840b800d000301201d800e4540403c0241840d552883c00352019460801219203404a00b448000c034080d05010b85801000714600b048010241241803100701552000c50785041c0104140402d0350900030f0000442000003441040050030034514800000d250500180c401600d4410360030500e1020b40c1404601030341c5420204442c03048a402c1c0260a1040f0000002d400901000400c0d05d200072030001d010f181c0e01c1d1a02681e64065511000303000e0b450804001400520456075074184032419400e40c2e160035566142d4401d400c51540201e5160712188059100b185060b1145602d0032030210b440c906c01c0520307080040e1b00da4038140d001d140500003401c00100d030507405010a034095070b409044d00e6107909081042c42d03902d40250352804d01610030350340500280340002240c100b810780141e40305840c076800c613801113845070004501503508 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 547669370 1250 547668120 547668127
    0x27070e010203090f09090109060c051312020105120a150b360d2109090b030601050105040909060e010c0306050111030702063a0b031b0603010902030c0c0610030209061002150c 77
    0x80c40c54050b840c003501c002ea44853321840d8590300940d05242d035034401036001e0600b60505c3d0050360003000b070340d040440107401000345a4940d01a0000740418540c1c1e044800440b150202da20a4030340d0103400704000c5600540006031090b8012a41c3c03000c05c4451f5950410b00400d37148803450501011024213104280f11800c1e520500d1124a04182828011001c0340c5800d909001c550075500c01c3c108020030460040c4071552620002030f046100c1c40c0100c03c10a238441c0d941c0c2003804050380100c2d0034106810001c01c014000d030302e0700800400341c0b400307424002220128a01240305000040d10121900206850301d480404120058406200012926003136161300480c612284514207008140074011008038050088404050901c07002c0f4800c44005524601e07100700707640b01c100559054a02190006030341c2e031170f810707809400713400717800b88103141d41c400d20703041001c840082c1c610b480450b0310a99a5003026151201040031000d0080c442c070300141e1050030012b20301c400302d000c100e4120b81070441580c036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 547670620 1250 547669370 547669373
    0x905101a0901030c0201140a0e070e01030f050705030a1e0f08210a06030804140301060f170d080606030f0403090f0e1b040308040b070227070e010203090f09090109 72
    0x12100c050300c82103402000864400708550701402840748503144d42c07000700314a0031016810803541501511000c20385590381002031640c2002c1007040060000304101040707540e96854400719010381440d007120075000780100010300d800e00085400700c0c10760050104600c44a0b0041040c07c141c000e11080d145109401c40740404100304400070321081d100d562424181c0704180d078410315880d501600c008850361906108002255802c026182501c982d00c008100d8980c6d00070000340507100d990000300085049102c0020800034080e108005c140030391043d02c01c05c4d02c40b07190980741760704100c415131340203e010070004400e1140c11841d51707486440303170078007042542d101d071a030605c03542c220307081031008903a0503050107280341a030341c03511070740356000c1a40524050031603031a504140124401d00d1810100407a015046548402e805200141c035400e11154000024001e515545401c5d90000f0106070320a4040a00f54404000c030b80d140c44020b8050602c11181d60207009100d08002c000705801c1d545c8002100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 547671870 1250 547670620 547670639
    0x20906070302060a0b09100515090406270227040f020f0a14070302070e070302210a0f0b09061c0218101205060604181a071403060901090510 62
    0x1400e1806076000b008980b4246180c0d108981d8107000c0548500c0e014410000303454035904154041d190155810008503444184400b050700400d45002e500a080841c041440101607400f0032948004002c1600300d8100701c07506c50205c0c8038054010a910340708080391446100801c40e07a0308200c50150001401c0c1c40c24141640c2260041105c0d01d010560000d641d00380320380d00004485607035501010b96880c102d80d03a58040d558582a00c5150f4804c0303021000030340c205000b50705035a400014010044134402d402107070030000f41811158204410328020b03901070341411074800c40d825003002130040c55458403410100301c0f0901c14010341c50380941b060910000142c1b0b80d010b102003401000d00101510b82000c50f00c410030b03200e80b0780140490300c012450110104000082351b0b60000c030143e400281075105105000c80e01c0b44100b0b0b000c1e00e024880c0034007000268640c01102d118044a0b030343e002100c0c0082210301c00034807003600e410354032014041c0140000026136110b6500b0800e0580061450b566501144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 547673120 1250 547671870 547671877
    0x909080c0d0503010510110303071803050d0c0605161211090a030c06031b0203030103170702180a06090207050c1c0506070c02100905030d0806042013090213030f06020906 75
    0x70030000b003010004000c141404440b4500d44292030900030002241481440d64a0000070700c00ca040181034581040d2140f4030030050000b41d504002620091254100f000d4010702454504903001c501e481d000410701d140703214400398400c1c480c2da100d042c0ca03541d09402801a003401d442c1341c00707103030170400070301249907a40f42110340150310604800c000c00c0c1c03a1240c0074045928851460046010a191005402c0e602004030780c152a0303c200b440524070022140c021081c05010002504004a08842034041c7c01d1100801c2c804c1812100510030a0b440c3c00c04041079010303907071009040d40e0220550050501e0b090700c00507003038981d44007183d4600d2610b48516140903403e942c840d0108041c88009411741c102300c039240b4807121143c1403000500b440c1c040800e540f884114031200420003201e01080f0f9641d501d401200000d4407000d010800d584a00155000d2603204e685440c2000940788c0000030302da00a402074403110070b8110780c1c6c0110300d0700d140ca440102c040d6201e01101e405500b00f00d9504103682d0107015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 547674370 1250 547673120 547673143
    0x216141612061e06060309150902062203020d0f02030705150706110c01111309090b0105010305060f10020c0307120503090118030b390405010e010c0203190510050c040909080c 77
    0x1c11f014030381c0e0401d00c00908115141903200c50400d0301d20805612400111080641078980c0c030b09000b21005140724907100c00b600300952028000c01302000748090030031584003150085099402c0b055072802048840301d0380690641805206200d414003040d01da42c005400c03002d40440c2d040c0313071140701c000c0c0c5401c652480c40000002c00d8081001920010440000f01c0a411040c008000c034401e5503d5500d040704052141904158072000010140e072603c500c0000d5009000c1c2c21629903204111000e0340700c0500c0b249242c028866008000740e02243d410b100003030940c00c1006076141c900f6010044803024881140d00034855546d10300040000c942c5800c091260044100701948240c10b5844c00280010f07020355101e0007800c101c0d40e441e80d100b4007000c0790200c41c000d0802202a6014800594100d005041d02941c103001e58420f101e41e20742020b01003031030a0b2040017511645071802214504443c000e840c0c4840018060005100c101180e610694074507000e55542410080c000c5059450301b13140088 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 547675620 1250 547674370 547674377
    0x30106031e050f010204060c290405010c17190b0619030615261806040b0103060b0604080a0b0613150501020c04060b0d0f0216141612061e0606 63
    0x901105100c0280f0681c911800124003d61919241110040c46040c0c003540190282d54064000c1c040140b0381100b03900c203814260b800305a41e02d054104503008011004a0201088200341e40001812403180d9040c40b0744d1300e0008100c081680c024901009010580c09950025030030404415611150f800149a03040031340d50102e903107420043c005048081007200700040c001c442d407209150348100d14011142000c01800c800695607003c18665014041e01020540750207800e040c0320500200040700d0781605d00800c814040341d030843c000d01209103d00c4c455558030b07801104020000401c140e546075008a001000c691613a000d802c0c03c17000729404803c1c00d1448069080d4100000e580500c11040400c408480c2008a02d141096008451043c80c5860b181c60350340311a11503074042198165083d0011450001032080d21740c0c500140342c002003100405040c42141d04024807082e2080c1300005841c1e10212444040000356502e9014007600600120704c10004140e41441d2035692060340300501003680c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 547676870 1250 547675620 547675673
    0xa02061602010e10052d040b030417040806070503070215010e06010801052403060d0c0f030c05150a03020c0a0b07050d060b0307020c150f120a0509060103120e03010603 74
    0x1002510070481001c3c1140a00141c040c00a00e0725001010345400080414044075200f010200803007401403025401e4030007035000715000c600220248061361180b44560208444805041d02045680c003031445560f00c641d1068002810b128420009141c0082c9540100d800d0740c80c9c03150145151a200342c0241d14405008030411406681c840060340c0144829a1003104068281240d0035001c00142d10122a015000001c106151118040410748030303000300018500d581c580b50038190780340083c0310580341c2d081030980118a13494000307400345803010164060351526452a5040c0c0c0030307410045d2282c41d14050f2407003150201c0c5549081602c907450641d2442e940340349040001d82140c4142d081200d40850620802c82880c1e000a00d4800c0004d0803140701110118403890720850748a04040302c8080c210114140c0041401207801c03074086d486060051115989450113035598040034400503003500031810340500e2460040c0e40d480c82843c006000494216100d46426500300a400e509a0210a054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 547678120 1250 547676870 547676873
    0xf020c0d110906040e1015050d0804051e0901051e0a030809130605030a02090c04080102040902040f170601060809010b0901080606040501050a030b0402040c110604061b141b0a020616 80
    0x40c207041c1e00c048112020400c083c85c07100304550b9001c03843c0428002503960310b940200341220360012401440001c000e5580074006141842c0e054110340f0070f083c000c0d1005240c0b0480c42046030080c1684500141c210701030380e86071208000c41c00e4004441c60303941e20080000030802d0780395079001c08040c0d80240ca048d551980352606100d0151701c050300e2516440c1c039001d01400107550100d88260003030b0301141da140d0543c8880035581d8030b5101d41c1d80508150740c030000d000180505c19801800440700b5041400680c190344040d41807003d03a2012a000b4260409401400424064414940c01c14004800042d0020850f030100710030050a030040e10039a40040b0401443d0320303050007101d02402042c0c0e094a035061650366a945003600180000b440380d503c1c0c446a14005100303410003032003558808100c890b1402c0c130341041001025008054500414070300e0508101e207015280c00103500c02d00754a01413400c00241d009092142445000d81c216000382107481d009603507644094001c4507810f185d044c0105285 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 547679370 1250 547678120 547678129
    0xb060d02072111030405060306120a1202100501060f080403140a09030b1b07151803080609090105010803071b0b04060503010e090a0b040f020f060406091706010b0a0f020c0d11 77
    0x140301070501000303009120250610343c04819101143c0b01960090b8a9458003400a0034606a801c04114144520358140301031084aa105040041e8039409442c113054645900c8801e45609008540104684040c21b00d203d42c4035060b107550081c064540301d00c401c5404001c0071510350155000b98001500310809105112005940c5608103184401001180b02115441c117014010780d1030107007034034480f4210a402400c00c0c0d0418542c0748141058981411014600a01101d86c10740785140035008000009100c644c0520415060701c014000a608080e116501c80514044041402d004035000410004607041046c0150000d02940d4550503101d42c100f050001c00441c00030900d0311203503c454200408200e10402664210340c0040e4091403010080c004a0040380402d64401c1e0040c13800180002c1890f403002d0820305455086401c1d0095604a40500340c1d030720003c0c01a0441a1020070049041c20b000700110f003030340c2c1e4103401070381c14260600000810b000d090780c000f50765800b00010740f060240781 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 547680620 1250 547679370 547679423
    0x180c03060a060501090b0405090720030d05041a09071a1306080402010f230f09100f030c14030c03091203010308070605060319080c0703080c07030311070605030a0b060d0207 76
    0x44441c6c1d05070500740307000e0008103a0749000c0c09050500c0540038541154803100c0440b58030401c8030341c08913944c07820022001030050208035015510240c0f82e010210081040c3c90881d4020704001c0c0007000c2242c00c0940e90b00c07442e0360f2001814046c080030030074207510246103416000108090345581c0f80c28503007070000ad00b402c004601c50700c04110387c3c02d80d001c88110101c046034401c1d2003000220307521080310600c891824400c0e202400c0c2c0c80023111400c060a203501c9640906864030b55a0280003400b610344040d03d503031031082d02440f031891f0240b000640b00356060000e1540700c18450219501001c103602d0000940d442a042a100e41c00001806414044180039040e0410020380c0201105107542072420300183c00303c44021b242040000c0c41e40c403030f00000c004800165410181c0d40303540d504407110056458a040c8011004584c20841c6204d1666012506100701c5909071202440c59807a1443d58009244403583e4503800681072102c0040034071948040c1004a03c03070410380000400207105510120f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 547681870 1250 547680620 547680629
    0xf07050d0b010603050a0605041a1507030503240a03050d14090102100911040c0314090a020d110d080a020609060609090a0b0a060308031f0b0f03180c03060a06050109 73
    0x114600300080280950904645181c60001655220b541459014061a51041b80c1c814185201c2c0400b18088807040413002404030303240001e09082020108540c060b01502801044051002130101c122100040401c2d0b0860031222940750300d03040021b0340d0312a4681050342d044c1e10450a61100c940c00405c0003080708050002c003814040c628000079501c900200061212548840110040020780e500d0000d100c035005105104003074400340c00400800c0341c031041e0b140c148103139030104000c000049150740c212500078003403006204107030302e03144809040d10300703030a400c5441e1040342d0021424010151040c55050b501a001324142116107514143c005801c55105101c100d0510101c5000081e05086490f48a01d41110541d0361055641c0203101c1a0b001500040000040000700d2103000c0301e0004000c201c0101480d9580c5075010f1050032f000c1d41d6416040c250381080440d040b60a000b50141ca68141d8004a4000103075010210741070800076107203494519290700e800d009540e0410805c034090b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 547683120 1250 547681870 547681879
    0x60804031d0d1b03150e15011d0907260f070f171e010b0a080309010e040207050a051506150f07080c1006061d06030412050901050c07080f0705 63
    0x1c41410700000c0d00207041e620020700200c811401c103003501c0314004103200110340003800c50f007034451408014405412004440f80050092400d0340c2d01a118a10025040e01c0c100041e080e4100301402c40e0302d0000c5406840300000d80300f00c0034000740702c0100e1105190f8030b85140c0303c1c25001c844010070140c41e1104001148044e82c0181c44203200c207aa840100e0021141e80301c8200c02608140c443c9a42822100700c180107004c041c0c0c00940313000b02015001000650010f444140600f070b5240d0b0601d44a00581c142c0e60700060480700c643c0c81a2402d40c0241040342e0098058030103007402ca6980354038213a0064070040791114400d00300002440c10400714825244c16601d200d141803038040d004a038500c0307100b400400300f020110b0021a4070000304038100500204000421403540c80e54005401030f51341c004c242031412031941c09983c0900b020740580b406103510107410f41c54502c0310380d4191050341004000381d04100051203448104481080080002d103441005440f04001c450207580c20281e42c0d40005004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 547684370 1250 547683120 547683167
    0xf0501142401080a0906050907150807050a0507151d1002040806040b1e180118021003050a150e01030b0c091008070e04020408010c0e030c031011070b0106080403 71
    0x3072410010102074451003480c0c09115035999443c00700040042000c00b900e02841c0a0420000c00740c00941801a14495142d60b002c904554204a5505204640400c00558144035440035280a000645403c4d4800d01e4a070040b200040b103580215002c0c0030801c0d00c03103c503000148800d18010701400f0250340d4403080c02c1d0314140c00d0000407580c42101030030081403280a50006050315005044602c28562003200c202070a081180d0100e14541c0840201701e495440c011880524042d0b24600c02641742e0f004d0401020070440003400c2d00109801000d00007240d448081c04807803000a407000d8006007144104924465045060080003441c0c000c15202e100602002030300d17065592221a9800518240b0b40b80d401551003050845004258880c8203070000e0001c2400700e00100190400b4491542aa0b10441c8a50601040560360200748680c690150000080780c8190310781074204800e020551203e061600c1d52507903624480301c1d000d9120800146040040c0b0041541c8992a0400000c415800f03e41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 547685620 1250 547684370 547684411
    0xd2406050310062109080304140703021804030234050303120606030709051e09070905131113030303060509010f03020303040e2203030506010f081009180f050114 71
    0x480705a5000b41d0b814000084445003c2d2407004e00f0089003c1008001407190501d5403070301c841e40b074000b034078101c0c0e4444103190000f00c174640015540c03045940081100150f40c1d1201810a03070081c0181040d01140204402c2d06c40400d4068850070f00c00c40300381c810f44111941c5110085061400386c00091080d0401c00040d04442011410316412a130200c60303c0f03650f501c84035030070f40d0081c00310380c441c40c1c20034201040031400070303a2ba40800c080c03090289d802405980c4e40001c01c840c0000240aa5544228401400c071840829588400078010f82480d00a141c0701840a1080e4440071a81c8224002034aa140a005030b06183c2001401422903c9029102e0703030455001030f849000d140a145504008480010103001c03094648801501418003145150132250030000d010345030440304e0501007010000441300c02807295001910540d040302c08090b2680c18165001c01401400071440d420503480c80c240008034103204c6140800e14401d00000982c052215500c14500c03030000c10098400750280290039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 547686870 1250 547685620 547685641
    0x2604051c18030615090c0503011401030c021b220c0f08040c060c0602040306052502034006121107050a060b01031b030504020909030c070e0a020d24060503 68
    0x7094035803003030000c1105509007000d080b02c0314459200030491810451410201604600254141e030800303404d81011600400054051300d4480c2074100c0164080c0c6103060304030001c00c48940c464100202012607050382d2100302c10480301d42d0050005c0459684004000260704941d00d040000c0345400e08440b0340c03916854000142e2868440d0700203118a0351504030811a05a040b180a50390000c0c6c20480c5050005d006c940d424004081032030948148410b07010380038000401d407100e0b0401400201a42414403d5555203140080c0e06400061000c4c52100c03010100c901441c0050309580d603031160300b0700122a1180654441c50703056081e5040810061000c1139001c644080d0703e5801480103d81d000c00000100c0041c20b01c000810849c80c9007001c000e082d254103420440c090743c000c6076003d0894507040c040c40d49910406098a0303043c0d000302c600700728114a80207102d40c4501303c403000604004280c801c08060340d0124002003201c001500701d02058896029520010781100e103452420f6150500018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 547688120 1250 547686870 547686917
    0x105090c030604080a0f0512070302070501050106050f07020f040905031c11070215090d120c0b0a0b060910030f0615020f0a120c0f0602181813032604051c 68
    0x9020040004698184075021f141143e00440c1e907135894060500d400700d80240250800c4508480fa542000f0000410031310a2090341c2000781d60140d0540f4020700c660030440140d00b0b030115640c01c035071200b070f0500215000388081c005120300050456184201c141e00441218682d07680c0c0200b108042c000e0002680710700e144100d902c40c1c00d0040950340e18803400000d041c2408654010050614907405801055005111403801c5202d227501000e2a195680e48009131864507640315000a000d10030402549800f0555488091460600207503944064000100b650b2050f00484104854a100600c000f0360421922003441d610b60042c0030705407030300d0ba1418a640240c0d48800c04000c0c003201c1070f8003808110300081c00340c80e502900c01c56030b0f40104056800c105200c4201c16104151b1450700d0440b100c00c0c0d040300340c4514000c03405801d1070702c1c050354103540c114910f640b0301d14400c1e0070100e6181e002400d102c0d0240128005e100401203400c48100075000f08140000c80f00420982004444400483d1901d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 547689370 1250 547688120 547688137
    0xa020c01120e070b0d150524120103230a030807081533040b0406032304030c060c050a0806060c03070c09020409060f050f090612030a020105090c03060408 68
    0x1e2440600035507100005000d40801104460141800014405941c4001003820175140b600c01d0002c400e00002c075504a444500c142500035840c00c0815144020005900440b68050318a060510010503100003122000340c1080f84c7c44d60403056525402807201007000c95000420b4001e02c1c41c0d03403c50350014849034029121005001c0442c010802160040880075000d42000c0d1500400100a800b42013400c2d00303a0380900704094810b0203c004410720340044900756121040b00c4e03840c1c140381c01d40c210010240c00e08174001d00d0420700352540751603182920041c081c1d0f00070f50b11480c0d4099582401004c035800800900e050200400c0402006900154296805a412904682c0340c00400c580e60740ac601c6590341c0100950544a800310b4141c1259001d0000c0e42ca9075042004815168030981144c0b4103a40a840d5001c5000d4511124900d800ca070603992200002e80a0750605210755007042c5160802c08041c03016035103504c104040d0318030400021900c003d040740104210300742070b10b038858207100742c140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 547690620 1250 547689370 547689377
    0x60e01060c02090c0f0f030a050c03061f0c0c06120501210f1103010c021509010204240e150702090a0b100507060605030601060c03030f14070e040e030301090204051002030a020c01 79
    0x140130541d0000030340710040701500380281c1c0d40704040d142044075402180c140d640b03036251401188000480e0310959100394009001d51061404065460040300202688442000440e0744a04d0000b541c032441c9800504443c0c684144108035144050207440c0d058004010748160400340000f00315529030600c047d10340010001c01510b41c603040c100c40c3e2031221659603030550708206104141039400502401d40c2c58070541003030131503202d070f5040a081c0d00c120311803194030002201d548849003610703140e140781c0e1684606080030a4070101c40070651595a90440e0408802c002c00d080d000e40c10984003540d0302488042c010803085c81c00100051070180c481c181142008030100b159403c00065501205c09041d000f0112243d540c1d69040041420804003c2203002900300400700101900e1801441c2d540d11000d00c06404a648001003215079014200726203920a4880800c0156030b9401d100a41c0a00210700015a88034201002d205844600310031200440d03108002000e20300ba800b10307002c4215902403a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 547691870 1250 547690620 547690639
    0x9141320030109080313120e0d02010e1207140411090d060b0111010603060c261501020a140a030e01020f07050415090c0f020d0f0e04020d060803040810060e01060c02 73
    0x120b4010050a08003c1c900b40b400802d103c14808040080661207120711a92031840c004501d08888031040c8001040e00305114050038001503018012a4500c2607000d4400c3c028410840720326450140b1030b030311682042075400303113110903070070103016100c03540c003407260500e2820441d20041503007804e003802d0182450350340340d1504109a01c00d404005294400c00020b0019544904002000740543d04002000ca480d103004149140064042036030020b025400d1001c141d602c103943c0c0040711440c8080f290450240303800c80030010b000902545001d025507002060140514600036010303c40a01c83c0742c2c15980300088030380f0700c082e00050301c0043da80d050b038000c03600300d10088202d041c0311641d8204c4409582000c02403200c0c42e40c0290010010001d6030b088502d5408840b005550ba668003054100018a00c4407601e00c8a04081e001018144003140002814555412050b4210381040d00700c03140766000b1405082c10506640182006000c085922100651404001a0070310a50310b600030b00405c0c2e01c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 547693120 1250 547691870 547691933
    0x803090106050307060810090605030c010305191508070608190905030d0f05040b0f07091703190507050f1605010f1107120b090c0105070b0901060f091413 68
    0x703401200003000043d045034201c0d61105000b8210403401c545120307801140610004400405000344411900041c0250160354400001100030b03080c0106008208515414030448640051050303034413058901600550247c00d240d607060030310400e684982d0401c0040350600c8000c0c3c8441c110700b4102d0110607030014507440e061138a40e0860185030b01440c0c0880c80c0c10070208a450b003039000540314a2245055001e80c2d80e5480c0d140e0040002507405030300061070603c0900c111a5450361015840402104070703421301c000e0007690032088440c25103800001d90003207a95030801030104002944618a01301501e010304284c0b144403207181541c4262810881400c1134501c07414024038140c070080c822802550482500e4114504034109000e008481e40e90032517000032602c2e0300c0031410450403601656001e241c45015220810b003004090402a025543e03400c000540f640395045840080c01883c1000c2010041306110481654001301503410580d1454070800000e806c0000302d141c0e00002100070109404803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 547694370 1250 547693120 547693123
    0x41a091b0a0908010b030d1407080d020412022704081b0601060306060f0c0b0604092102010f05090f070b1b1207110a0f0b090d0b0a090302011109090103080309 70
    0x102150280200081c0324031a8076440058101690010b20082c85050079030030500d40d490346508114400503ca43c020891903040e80e1004100440c01490500d003024800d8954004903481940582d08560400c46004118201018680200040c65880380c4a0024141200070400c400400017000e89100080120703036801d403501203801028022049030310b50740e111980a0020442c1d07000d10070115000030f403050081031183c1d06810340c865001c000030032151141d1060001421190f001180c0507a0010910412203c81001605160300c3d02d500219072446c13505a4441151805001e11005400201d108840241d000443e441203445ca05107251b550745811a60080d081c80034004503850303004102d110065060540c010305145030007800c00d00e00800c0390104004100b615840b40c0e4540d802203039000c02404540c034000e004c0301c0d5400380120305800c501d40d484401100e0101c814804160f6207401100c141517092140d0b0030001d40380d000039880c0480c080c0008030003480510004003070950000010b10b04110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 547695620 1250 547694370 547694401
    0x601140a0806040f1b1101020f12070c080a0206040b1602150403120908070c060810090c0e0d0b0a0501090e0a1b08030304050604150204031104092f030c041a09 70
    0x1d40d00c108040c0d10800da40720b00005254140100040f100c0e4a030301b040f1107040c801c640c0001e25801c609031520300c02c65201803036000028940710a000040000c1c1c0003040400d401440030250b00e07405401035241604e8810340201006c2c140000b000c1541040c10105900000c1680c00c050300300c2d01807030300ca9503949000c0700d80c0400180110103082c20b1034015410045550080e0400c140b01d4020f410703400b61202012900c4184c201c1e00f182c00d1030b944ca41300304101e201580c042c000343c4000b40f400d04542c40c000c00100e00100f1700081c0440380c5205d500c2c200541080b0901c1100c0c05013481080c14088144598002907603540507100c0501844000005d1410300402c2c45244001011f0860079252030b031409007045038460074119401c2d01c50611000301c181d0800010b2084ad41035a03403002851201c0da8610090000a00146400b12038105080c07810000f014516000107501c0c2c41b843c440c182d65855800c00f4076040c280280c00c040d00480c00c2942e28036100f480014000c8214105503210452980d5002c2c2040d4441c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 547696870 1250 547695620 547695641
    0x30f0c05031f05090d09170a050102120a0c030603020a0b0d1401150809151303110619060806010e060607030504030812070e0105070f030f0c0213060e0601140a080604 73
    0x1055111903103030001070144582d140e60007a00200b109030780d0f03500807030b40700d640caa071660300001c07605442405112404c407581d400f603110420440b11828030554640b400c9070b01c424801a05414131030100040c401c103900825003507050518042c80308900d5640410109507180c000d1035800400420005408243e980c04001500d000508401e55941c0d996510b030380801e40011294001b840c524005503c103080081d00b0044140080c038424025510b00500311504284040e04800704500b41004103e203020401c0800e02070101e98070f403050700501d810000390407200c880c0e02103c81600044010803d848900e0134940e400081603d00c5951110f46240c2226075201d2504010142c910100d80381c100c03030f20701004151054000d900d52522840d00d9000541d00c1c4c2c059110001d080980d58280a000a1310801ca11040300007a800c1c0407184400513070018039a103640385002c40d00260786d01c008001800c580c110064000d2700038204600036002ca81105120b500c00c1c098200c040c410000042035032034803280d00459084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 547698120 1250 547696870 547696873
    0x4020a081605070812040c0f0308030a020a030b120601050109151e1b260c03030411150d050f18030a0c0804030b0a02271c11062208120301030f0c0503 66
    0x4242d00c8000f0f120175101910180c0305d07510394540100c1c0503c5080d81941c150380e00107024a00715520f03800100069407000d14107030209603c642c4e50740000c0c2c40340c45030807210003000806055251b041100042c105d81088d40100282c41c045000c000000390080200c1106410300440030300502a4203009030351040f840c0c018040c44000642e6880d082c04090a0341c1200c6400c10601c41103140010400c0304051301031400f140519400030404680024191640c0042d41c040c0a025607200820303130000100305402104c0403940081e00d5a0400070101569000d4036840901c11102d8009280003602856480c003d1460880500c0301c00d500107824024031005540003140e119100c00c1003803030601d5202e0042d4204114404502e00f41e002401140c400f501003800d05548060103004a098044d070182c040a04080816691102024503c45c0c094039540020b1440040e02003034a89110880b588100107801603030300000c900d8000c001008401581c41d421241141e4028843c0c0f500318420f804c0c0310740800515804103525 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 547699370 1250 547698120 547698127
    0x10060804020a0812180904031403041505070e0406091a060a021510080c0907050d2705060402100e0102060f0903090a030b01080d030e30040e0f010504020a0816050708 73
    0x581c0d41c0b60009101c00c2012072140c080341740060040c05441101076500070085008840001a80c01401020b594072900501d00080d10320480e0045008442090355010009942d8240707811140c20305008203401400741050400039252032418105581c41100e44040c4100000a0600740c0c8070700c200070020302001555403804c0d66080001200705992a1391007150081c0c013802d2044070051410408482c85400652505850615683ca03858010503800038180d01d210301c00c07044c000164040b6030319821414070500050415003054010011146a410003000400a10078048500359074081202d0303420602c03040e0041d1003900c0d500d0701c180c251b001d009400781d00004407500000a010514a20314101e86558080d00c0303512152040031800e0790241404490385500480e00401540030242d81003034201c1ca18200c2d000c0c880b2484e030860f203940c0c1c01030340040c4a405a14007404030030748001035280d00404d40fc44003140303008900b400150401500a00c1482c0c207030b244030b0035107112074010300440e04103030b030b006100e581d0307 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 547700620 1250 547699370 547699393
    0x11010c120504060f020303060102060406020c0a0b0426161203062c070306140f21060a14090c0108061f0203040812070f15021b060403080f10060804020a08 68
    0x101e60060f1007000000354664050a00da103001204490003410103a02401240c0d455480d010040d601040f076114540c40741071691030202e45411141d41c000e922501403a10986141c0500ca5100d14030304001c5400710400f000704c100603850621076444103070b038080c001d6054070300310036400d0b001800c2c1580705200700b002810321811694481c0c11130306007003081c05240c113a02e82c81c2c181080b02151081e01500203c4201c0d09002c00391860301040454510030300038101c11500c120360001d01707400b409400c505141d6900100610011582501401c510341c004904008510701d080d203441962501c09030030450501103840007091007611014000e45a10444424100d6206e11002000f540c80d031141c841c94400380102108280481000c008882c0610381080740e401d0380c00d8964980c09040e00c1c00d00c403810090b0ba800c0101e003290702c0101002400504406010300713154a0305050151000d1401011807084409210800000720840070081c01940c040c0e203089800d603560352020824a83c580c1d009105188503c502070780 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 547701870 1250 547700620 547700627
    0x20703110f100809430801021902010f020a1e091703070506010f060215070909090b070f2c0301020c030c0a05070e10091e05040c0504062111010c12 65
    0x6004009890480303028101300040070800340d10288480307200c0c1140c001c0c0325210304082c060405c825502c191391160003596a903200d508991003468500301d410900020f1060035502880381a0303880340c4c80701c401d6141c00c0000c500142040d1050840d41c01c4041c0702000100b4452144400d2406014400900140f080349040c00039a00d80065008030b4a91186030008190071032040210382c00c81e0465001030155101100c19038551040052844040140c40c0600148c00d5080e4040d0102e41c5001d8041d40081d410082002000401c1142281c070a120607003446c402009a90f40c500c244102c071041203004204003420001c0c0c007911071400038905510000c180c10000c0e46001c00d001d180c40384280304651860703a840401e254500e06c02c41c0c0b2207000f00c0e0151030401ca80034942c2c1100001004c0102075080e000c800340c0c0404116402070728142c402e0103115809021908040c03042802615000030042e01c2c5c10005031021001d15100d01d03008007810990340b4007110326400390314412007007584400d003141c5520701c414004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 547703120 1250 547701870 547701887
    0x1507020411030a150e0601030504140d091805041101030b0406030b0c03070305060118150c05030d05010e060d050703080d0207170c060c0408062701060e091507020703110f10 76
    0x104070a00d0030362090007007030144203410b04880701540c400305c4981d12480103400601c0002c0040d2050540d004850081031014042e0350851080d0f030703c5800a040c28042c150f41e440143c03c401010321881d00d0140002308407003425403414103900b483c0100d00d04030737594085400350006034001021176090030248540c003075508001c0c1d40f0681495500b0441c81d5590f500440c0c10008070500942d00300c40c1054188502c003110754240c00500b01c2420940600d600c103070307106072459229000502c0400e80c1c500c014800d14070030b13100c000e0f0407010440da520700c040b8540d01c031030b900c4d1811880024401c410004040d06065007540584264541250000c641c00103064900e600c0760340421442c614a000710000a0034502c03000040c0c030309690a0134028601135464200041c592805400c01c1020300026000b5100703101004d0040f032010b06201e40d82c4024600b400641145084ca19440d10012108030740c04000a0750340c0000d0b4242241e40040c0190007049411001c9008020807410440d000245055051510740d04034110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 547704370 1250 547703120 547703131
    0x80108061f1a1902191106070b0a1d1218031608060a0506012a11040203071701080a0809130204080105040605060f030610060309030e0a06020a031106100302150702041103 75
    0x8001040c81c143c0c2d0100d885008150703034203d03080d102e50b14540c0858030007075810203032001c083c10307040c039000681d192411031a1007201c03045155900c0351310b0038420724034520f01b42480c0c2621800a18000c1e48800922200d405801240780e503501c03201403d141c496800b000b08658022031401102c5800f520740a4141d1070b82e00898100f11042d00300320100702c83d0752048005550080c109051280000d651005040349201504030560b6110110f4050010641c0c0d10f1000318041c40e01520781000a0900000078207104105074000500d54224541e0034022480680854250320b508990306004210104c6c0701030020700030341c0c00c40710381586440208020007189500041c0502d80846072524229460410542c0d107480403244048038100000c23041008030b0082c1c0060540501c6400d10701805401c2c00c000c00e0400c4855404080141e0005d80041c0c141034026a0303e40f00e211b0000301811540c50038074001d803c41012484000d00402c0b0013401c449442400e0300c19140c60950044c018410807800701038644a64005855 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 547705620 1250 547704370 547704397
    0xe0907090e07090f05091f090f0608150f07110d0806040f02090a0504050705090312070210020d020a0807080c011b0e01020304291312030807080108061f1a 68
    0x442d100a01514030402158518054211030310700b4501402071408002e040c1e010180c00320380c007036440c81c000c490540c07002c0c0c420a0800034200160300760940560b00baa600810381038001c4150032040c04501ca42080c0d01280303c0d04046203a458401046450505501e105c09050280307031242800e842c3d200d020700d1702480b0100c9090202c240d1a021071000c9200e40241c0f00d9112100007001c01035820a90840d503406072050030701c2d600388019000440c1c10800000300300c080581000031800110319120042c000800011720081415041c3c10070013a550343c48118003d0010b11001c03500d0005c100e00c900031111718045450003801240315030b25000001092202407040860166000075405501c004181c030103d03010004035421440d0908a003507220400440c150411020400000420601c1101590f00502201e1f108a55841c20740c18002d040310400b0344a00100501d80004100c4140b00141c215080400144076468500254505e544240d40a61198034a50b03860f041c4003c14440e410041e0001035800300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 547706870 1250 547705620 547705649
    0x204020315271b1c020408030c03130b0313060905190302060732070507030c0303270308070b0613050903042904060525111c0809100e090709 62
    0x1014283e80710701915100b107002c0c90a101c0d100d28085180c070742c00b001544c0c0040061802d074880798410f04581c008461385846034000611b1340089044035010703000408003241543c0c25800d102c1e036950011001c0900c0030b03025548420040c000d00c03005000d144030440d81d810a4682c03074403091402a4480404441a90100d80703083c4600b609005a4080700c0780088c07103d503030710303400c0907001d864200c0f0307a041040300307454612400c0d0f408000201c2000000005e54080c0d00d401404d0301e241030348090007401c410621000c0c143e01d0242000014440815954140e5100d11b075800559903134000304200040c00480d540380103043c4414049048070210040040e155030806e210b1f000445104000015001d100321106480000c00c0104400e501c15405000019402c0c0d03400203509002502951001d400c064040c0d0b00e907444050280c1c01860280e032000f02d510045090490030354115207440001e40030720002c003800b60900b40207070340800d03102b00c000c803015000c000c008910a0920441c000c3c9030050303501549030400c0550 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 547708120 1250 547706870 547706881
    0x20d140f07030506100f0903080c0609060703110a080a0209100e040b060408120912030a0305060414071215080102030f0702060907270605040e010902100504060c020402031527 77
    0x74020240304500261400d501c07a9080c1720708440a8202440e000d042000f03040010000851810003000709440d03850080c940f48c00d040c556503080401c09006001410301d1b1000c2c501035800030005131864220b282c100503100b0b43e9041e011002a110b0804c20541c801044840b5400b280e4010b520301c80102401c2d0307401c21200e140c5070144480b41c0300314001c0c6071281c0c0c03100c811103140a0040c0000c180072070000d40b11301c1e4007101062001e0700e16040740220101180d100d10800481f41032a102c1d40324a0024203000708030703e04100002800180c1144040c00a851300d03070464040024010180710020540c0c1070086640e440c020041c00c41c3c1410681b01880103005860105404900c005100029a011200300c843e04040340480c1a030580c1841503c02c020603140d19001405584603c608045a6503400004c1280d5106204000c15a0401c00038202440b105100600a06070f1042c11081e02542c15900180d40303484504146a11b030100380d0034a580500380c034000f00a04100c42c0f440d940e4951840e4040009074640 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 547709370 1250 547708120 547708127
    0xd0b0a0c0309080412080702030d081905010320010306050636060d020702040f060b07060e0102181e03070303050712050f0904020a0c0b090106060908070f06050d020d140f07 76
    0x42c40043c00c406801d2105101e40e0316001420710181e4810365074540792400030390100c0c0c1040c4802d610040480c807403000304049000354405949440005800422480d0b04554a043d03c00030300750f012807020300b980416045a42d01030f501072005060001c10703c03a10f0320542084d01503001030100341500140b55a010096405130181c50414047c4001450385040030000140c4600a40210000384e0f4800c1e01c803145182a2907240c4600340141046001250f80d47d511814001c007036072040825000b003684100410011031b0341c85000440440c004540d0340d040c07900503141e0340c0400d0b800e42241685c10b0042c7d1400204158004000f00903882c400c00c003c17081c00501c50416110b50143e121a0078080c2c40400c44140e003440c09500901d288041307230a118241e070441c9d803200c825241040780c006e000350f9921103007804210340003c0c8800c001c1504000a00d851400c01400715003003410752080b103040c4480402c801c204001160103803502c07010500010440e2500341c040c24103c1f54815078080051003001c90104960510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 547710620 1250 547709370 547709381
    0x213050f0f03060f04030509061809060d030f0c0302101407140703170c0d0501080d030e12041a040b0a0e01030605010c03090b0d0e010504050102030105330f090d0b0a0c03 75
    0x100a0140609695004e040d414000008208074100807042240c0303001d690390b40c03010740010340d03252000486100200040c0411121301800f00c52040c100e046201001a5102d60801030407181403070700b80c84102c017911b410b91400d0000c0300c0c03118843c2d0500705619141300651140034400c01c12aa9030310703a4a00c000030b007000349124681024000032007082000303160070340c45025590000e240d07081d40c1d0f103070860b04045d007000c07290b007a00500314503082400400c42c0c4580c5402402d100018440c050408107030480318103100e6100d184185d81e206c1844180001c415449081620b0003405100c035800d5890340c00c4100182600907e0311101d001c00d1501c900800e041d44119081c0e940603038592640c641d010b040101046494001d992100350302d43d110400d4401094080c05881d019520074000580c49504040070001800c1402c0100e200c01684905e5401201001141c0443d85000e41481d0310303614800c007030090140b40303e848402e0381c01207200902c500c03c01912040c014851501100204400c80b40d5a0048040e01d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 547711870 1250 547710620 547710649
    0xf090403090510050403060e0a0b01080309030307060f14040b09120f07060f0b13060f1502030307030203150603070f02010f0506130e0106031a04110105091804030207090213050f 78
    0x1c580384000d11060400000d50941c40803541092410140d0341c0d990301d000d0700d001e80795000040e0081c13180c10080000c1d0022103400b501071940074500308000c46010960303c1c001c100000e8800754070740c0f85201041510794010300c603010240460038414034280c2008a8254000d8600c95064402c20211440c0d61414005652400765503440c007a1800f040c94880c400a0941c1a00d688506d543c0d62940d400c05039600c003841e02d050007075418040340740c40c68022070844000080e0b0213401c0720f06245801c10310140d0302008403580009103080060b03d075250310488402e01c41ca500c0c5603030303000302c6d000080c41484c6401013000002031095500902511220007441c0f0140c6d6015100305400400b02e0000d2084104150003180092070040000152950740343c0700c0204502c0a40303049000d244000307061000740003082c00c8010030504203003042842e003200d5070041407042c18500c405140190f0440042010144240309800013007108040c1991207100007402040c900c1d909110311403040b0b4410300f202c1c03031600700a1220030004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 547713120 1250 547711870 547711877
    0x80a0501031709152d0c0d08090708010c0e240412031403150901080a1a1302030a060b0a060c080a080c300601080402150c120301090b0f090403 63
    0xe407207224403100302e60444441668421413600100014010a01c040e02e070f05440c018400594030310056000d50980807030301005c0d601100403c441403500c240050582c1e54039030180341c80344090752000e000d541002c2c0780350080c903055401e000c01d42140551050301c40385039000840303440c0c40c00003110410000c01004c0e200584041c0c5820b0104205000035001e2040d4140c0c000e081140c5d10300d41001c0003014680c4100c42d40f80d01c0c1202c102001c451030400030043e601400080d030080626035040d4645c01c10041241458888910308980025410350064100d01301c56903001c0e00f2a006d1500c0f910300030b0040c00c2c600c21058001c5030010070000b400c92240030038210140d0401e0010345041c880210407107101000a00b040400b202c00c00908405000034484032500c3c020b03441036440c90792150140707a000b41c540542010f040181034814000541d0711000030b032100c0c11402400e0369880d40b070010176a05200810708008100c11001c0000030700d00b5a46d4200a04426040b00c204040e40408010046140415940074000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 547714370 1250 547713120 547713143
    0x6030c090e061306020904020909010f1505030702100903052a0c0307050603160306170609210a030c2102070b07020a0b010e04020d0807051f2f07050f030a080a050103 73
    0x400c0b405e5004115110740075001500d81003139000841c40074902a0f000f00c03144607800004000d6140103d010203071281c824500f4614508000358000d58480e54180200354407540c1315003000405002c1c0c01100c803170640c240d0391014010f94180d0707010782c003103582503041d0a42d0140354010303e070500c2c010901c40240d0f07800030078082c10760304c516407461421008401c1090625a40316000320311010300c40001120300c032544004000503c0c040030803a0415240200b002d1800c2018503540d00301500d09800e03514031081500d4002146840070034211000c8441500d05e814084a0141e0a17402103403940081070414051203490f0740f02d032581801240e540d003100c2000b178155400d020040c0b1040c90030351039954000d40000c0042c24106100d480351f15059001400840304c1d68003055020185101200061100c00701c0382108200c50024415280103941005c00d1480e001c2c1c000d04d00c0800c051150707609623000d80340c115040780c0d802c3e600c2c030070071503901d6009082d8580404c403010002112f0f5103a1740500c505803940100c22911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 547715620 1250 547714370 547714373
    0x301051b0906040801062d050622050a0603060806090a0209340e1207050a06030b0a030503210a0e03120406090b0f010f0509150f0307080106030c090e0613 68
    0x3001d400081c200d50303020700100700000e5840001d0048001400b0503074081d41c4903a680007204002d9001c034052203034801c04450810000c1c0c3d43e500041d00d41e0b280c6110328408004400300d02d4441c82054640090f94403071840f20001c50b4281d4583e000c00c2c10340d0b81c0038088445644583d600f81d691092030440095018001d8000500780019001d203610110220041480c0201945510860407107240d62040001680100300b0454a1030300b5100140b002404c2009450200e0400000c0f0b90a0211405104281070b03d60311041c1d4661942001e0b1401540c01c04246d03a1640080480380300d004c3c1d8190460390662003c1c6011034289001c40c8035021080000200440c5071041c031460902804400500a8a140c0e0f951a81000441c041580c40c0f44103524450701c0c0c118030740c18011a0065a0395a42003103020701880b0b4100030880340154802c3d40116402c03500e8070900042e400029103040c401d80c2140c0000e5003060703000030402c2051042a011f1380c02050051182c01d90382d4602603903c8100712110014042d11160400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 547716870 1250 547715620 547715671
    0xf0309060301210b24121e16030803010e0705030c0a08270d03050c090904020f150c010b130e0a022202040b07020f040507080c0c01091205030a0b030105 67
    0xf40a084504030b03105462a03c1e140e12420709800c031682d4040c107991030303800e003c00d04219003071003040242100d92145441c48551110740d100d4540c04c0031503000742c03041d03034403aa41c41382048080005003c0c8d0090100442c0c40b458245240c0e0820b20406001e44080d501090505020303506582c850040701c9031481c20071450300303000c07500604084c02e840c90408541c003041001010014001c005019140300030401c0e5001c511005085039401400c85441c0c11041c015800c2a03640e541c8240d0700301e84c0450352a50a0040000080c0720200c0b04d01e40700040741c2c030000d0b08081022043d0008400c18404031564030040004071003d405807180c100080390030360040703401c210052604003111502c51450180a05007031803a0034101049034420b4004442d0000040383d841d0451401d501c107415101e2003580e0900c99800d140c08007030300448c005400a45d1011021900ca182c50b0700c2544400020398101030050035201041c280070703010340e100361600b080b064103182c281852802d05015681c080c140c094810a802c902211100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 547718120 1250 547716870 547716899
    0x200a1208040314031509160e0f0402090909160b070c0303050d0912050c010f091e141507080a09110103020901090914061305132d03020c030f0309060301 67
    0x3201030010700c2d403c00701d540e14100c020f544550305284024802d42d02140411003000d5008051001c40d6a214010203002c0b5070181c4080c0e4941c0099440300d90816120700020041d00500b0a4140c00416000800211600002d00100070115081c3c1c0d0448042c2c960b6114403e602c1b175440080d0203688183d408200080c1318000401d0f89121181700003c0000c50355840e0828445640f40f030700000380006c100c00380d03c41402e100b40703100d8018107142000407c01e030b0368a01c40400c07560410000c0c0507681000141c14040c51211000b40c00c4001002e076a05140d983c3c98803996068281c1c1d1500000b40c1e05000510086124820481200c1d00200324000500d1500c0046020758400700d03c0f58100020341034002007040380c2d40258202da010000b299092841e182c3c0c1444801340e00c1e40034a826040c1400f00740204005003100c2502c42d10b400000098000d00c00c0e507264a080d283c07602c000000c1c00380e000e041034207243d8045084c500004044094400c903020908a841e0b4030701890ba20326510030800c000400c101d40070551030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 547719370 1250 547718120 547718123
    0x302042112090e0c0706180813140d0b0402010210110301090c0e0a05120a05031314011715010324030b1305070b40050a081f02040f06200a120804 64
    0x10440b1302d20040d500c440329049031401c5500c80d0b000b20f00c0307001c00c0301540b0840c00641f1403440030800300100d900000e601d00c0907441780600714800101c037207000d59100784408041d500071034100303001460842102811543c0300740b0a06040515000700502603910645094299507001082001d809040804001e0b1100901145000e6845443d4842c000038000344050076021488041d000540c030b10b485904510b22000b0460103040244030201e03051440c5144803142d0700b008c1d6000b10740305c4241501c401a0010003400d580d00c82d00324201c0c4101c5001700352030b143c0034003624403500e001c81440e00e4000c405140407412440080060300550028481009100d002d00041d691141100848859050a6020081180c130701c1c0c858440c544181c02401d600f81c9400c210041500303456901d0101d1030708907199107485013804260040010300303400c02c111a11940548e00941502c00c9d26034481a50b0750b0000e40346000f0310101681816540b40121092280858080300070323604904100c102084000c0115200c0000820 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 547720620 1250 547719370 547719383
    0x60d02130b1804290703020f041208090315010f060e0402120708090c0a0e0a0506010e040f061d04170a110a0809032514010302042112090e0c07 63
    0x2144501a580c00c2e00900789000312514800040c105800c0941e00078007000c00072041c40003c0003041030606800801590700000d50720b00143c6500610000400300d102e503a000b60b07010b41c180110a024814208002c0c040e00b0000c40c200d51b408221502d0501d500c84e0240306a060340180603108109140c05100703c504461030080c4014501080c19120707010041c415182d090018048200700302d01180100981c03a00700a0888116000e03070b2401080f501c103c0380c0207042ca850305889101007410740c1d016005441161000074418060310700043e01d00c070000d1101d4801c444107101400b0240000707003450f103140ea0140c0c0c2c0180030446480c20100c440c100c80c0c0d21981003041000160020240c2d1a4010300c03c0d505070600c98106a542c400d00714040518001450200c1c11400141040b48040c043c0d4112081040b241c1e4511580c0e01078841100690081c0955031107940d019004100101c1c5541c44a9a0402c03180c0c0f0619600c0451504072008903403450040c0540840d0a680c01d0121710140040006007501510400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 547721870 1250 547720620 547720631
    0x510292101030308070e03100b0613060e040c0311040b03040c170a120e100e041d0109020411160f111003050402280b1305030a03020f0d08060d0213 65
    0x800d081120140d60104030034016810014020142d1080840f6003040281c603081c0004280f01001a80b1040300002c003d01e0569104122865a00c0320750030b94101d010803150480309990f5601d0301420071505018454459450880c40c1c7c030300e1034082e06c101205403007115400381c02c090400140c0006c0b5072020f482690480c15041001801c1c0f20454818a00f40796510017412620085141150f011070038000c4a1040c4021100281029214039a03140414005450650641c1c0407030030106005004c4102c605100d00503543e54501e0072001500718181c10340c800e03203041103425180f0824942c0c6020340018a0307162044500706001040d504400040340c907006040c0f242c2c9440b03003040040c01ca02526644000407a8442c4200829450400008100d00041d030590032080800c03000c02003295907035400380200300540810445601c000900b0b0103c05804050211404501e45040c0603580e055a00003190451046440d0704140b14402e0716550b02654000d043c0d002c643c4066400c111441d0000300c0c0700d02d400b603550f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 547723120 1250 547721870 547721887
    0x90f0e1f03020d14120c0c090403141b151b03040312091203060512100e030d061e2709170a1101060e06090f04050f0601090f051029 58
    0x2c1107440c00036481a00a08000348407244c0050600b100a541520300000512189044036400300702034410302c03c102c07001035041d62686001d498030210108403002840011902c170782008211203c3c04002044031040390955420a41d800c2c3c085d02c41260003c4250194110b14144004407001440d08140b09003032864200007540b01c16411580300d14400d840151504004424076a010312070400581025100b609c0301d01c0064441942e204d82c200c502e2040c290303a600d002c102030041032064402890b00490300740012907650400d40d0310511041d80b1079007020031004002508030417005040c00180300780380c05045440040409540103200d01c000688000d403c0c03200340040300590390700030180c40040ea12030300300f0440c0042c25142165050b400c400440d41e10041409002d503940c8040b690700100041060405030b665143ca00e041c8441c842020f075507032080d84008550801c45410104206070079910030802566580c6105c51030b41c0d52071080360010111101e11640b90000d521000b801c0b00c445448062404134013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 547724370 1250 547723120 547723129
    0x9080912030c12030a0c020111030c0f0d0203070507050f0f1b04090b09010203180f190f06090f1a04020a030605090c0a0807050102060c04030812070306080307060507090f0e1f0302 79
    0xb00c0070f400c1e201d000000c00807021141d1107000701c2c91a0902c000c01c070204151502c0c40b1584070241200040000201e0940c1002001c4400c441030b900250070155100d05080901512070f8020401c00c039080d025003401c2da107046a00195105002aa01c0010301c0c1d02c14440c0f8000c1800e06204100700c1d0400d884041000104039044220b9014010000c0010b07968035000d041e4811414403515503044030b4106800d001701695002954a010070701c0c3c1220341c01308e48880d01e0409020440220300500850420140c0c03814031000c0c451a15041d406080880c881010440e0011744150044500943c0158180e07030a102192513a4070150340305602c0320071941191a04400140c101000390302070b03081c0c0d6021040a002c6940e05014544d00050100d000c903040c80c3c110342e10b103d520b005000d03903002d99031111000610000c1c0709800100c0184035041c162680d1f05150f080400252070101e45900105410010010322400149071000c1201d14101d0301700c013191142d001c000354400f041c0c5488000c01d00d0740c6c040400541d40c2e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 547725620 1250 547724370 547724383
    0x50603151c0807050d090803040b030c0c34240e01122c0d0c0303091b0b030609010e090a02040b0f091905010b090d02010c0f060e03090f030109080912030c 68
    0x550003800341d1711885200900790420b139001100310750000e0100b001034400500581b5042552400159290124005214581005031141d00780a64107104807000b5070400550001d0042c40d1141c03c2c011164454038001403041030141307200091009480303002c04182c07140020945012051601114078804002c101d0f054a034024002c0c070020007034840c2038101c00412030401c14a08106d5001e003002c01080000500400b01c5284040c060545a540301c00030041c648982910241d102400d150f000380d00d449158503660001c4681038055800c4a00121b009800c0c500400c0c13003082c0100c020090803800b40d0a10010f80380d03058a490f0400d0186203c50495035549060500c0703900c100601203291005e403052070040d01c8040e800f5900b0301c0c8042115082680350520000348980e020f003400762802c0c0c818a0800c0c00b0f940c10f2400600f03d81d180044072141c081000c0014141d00d2002c031000d0381a44450803c150894441035002019518104400109410710f002082c1315410600c06890502030707502c01450038200c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 547726870 1250 547725620 547725623
    0x1503060b031914040201091503061e151d06070f0c0303110714090403031a040f1a0301020306131d0607020102070303060806040308070e03031b030306030601050603151c0807 76
    0x21a00220100e070100c0750f00c103006146800051019240c2041d0b000a40380900500540040001502000b00014001c0d00a0b4006000041025401d1303942c2c80c54452800b00c050041003d0b080d50321000c40402d80c418030701c02403107181c44480310301800c4020040183c160300c1403100319624902d00d40c51038045896007111400440c000d40310380341d000710003094050800d804d54102c003110451403c1d4484464a0381104d05a0042d494140002c0b9420b88480000d00540b040c140c0c0ca91189c18030841107944969900400d0314040c0c03410211480703182c1d280030035090b070008542c0f15801244404c0d08010090f8070b40c128a1100e82d4844c3c00083c216104074296051080464041015030740025140c010150701d44100001080d06402030211400e20f6039006100300009800c01d030400ca001c140c280e487d0342d814402c4412803030314440320030f03c1c24490703a200c0f40c0c8070b4000305c0c0d44510078050784000113103038101802200d03c034900512046000b102101e08114400000141c02845200c104201400040c00f42c0001c281d180d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 547728120 1250 547726870 547726891
    0x12010501180503150a0513050309090403091511012007080f0906030f0f0c0403021003270c150207050616050102040e090a0627020d11280803131503060b03 68
    0x505e480c16004082e0f43d4090003100071074448100c0b00010400100680e482e901044400014903200c3e42421101590325400c8102807803032610b00c50b01d4150b002400504000010304c000c0c0050a1240c041181e090317540c00301c424900d0010400240010942c1005240340c903200880c0500b0a0b0080000c50323082e4004455100000b100e40b81400003040c3e900c480244c2c80401001044c1c0b40c603003580d02051203084120200000d0580300d050000d400c90301042c01c00c090703056800000d02185050f09201503580c180f8070883c40c102500000400703d8074800f2030000c040c0c800180c850380c58104603001f444402101300106488655082c0004903d00c00018086c9020702100002013018188030704000c0c0403201455501c05010f0100380b0741150381e041ea011040280b40d0122403441044c0070f03905000c0a00c0b01796228640d0b100405002510481501c84e04e4400b40702a00c04810401540b21902d0720b90740d108042c0c044084880000d01046904200c4500301c203223a01e1b03032402003600c9542d00444c85240d0800d8440d103821 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 547729370 1250 547728120 547728163
    0x3030705030c1b06040f0b0702031e010b0f0f0109060c06181a0a053106020d2301051815041103060f01050702090109050c12070f1412010501180503 65
    0x1e90461602c28000e82c50300300c0c4d0307040c9400d01e07000d5801d0b40004640303c4d03081d0801c03000c80c1d884150f64050060031080c01842014488008003914414000c0c00803107042d0b40f24441055a900700340c24044a445801417068503243c60460405400340c403013010500c4104ca01c55110988041885001580c82c807000303215840881c40c440b440c184091221b000185084070281c42d010420181c60000320b8940d01108640c2a040d414400800300301485d05c084030006029140000350320540c0c00d905500901009141c110320300703081d0340c9a0a001c20160b00030711503d5480b5111070a0b900d81100c440c1440da0b0001c4824503124400139980002c102520482001c1030800c4401004110890515100070001120f09281807403500364a9400039005400601807520700c2c44d6207100040300100440308481442e0400c0d8501821071420780c10051146140c0700300f490008000b0549840744900071410b80b044602020191500e076800e0000441d40004001c2e4060710700300345a24001440c1d00c00748070b105e01100002014031103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 547730620 1250 547729370 547729393
    0x903080f0703021615061a0d0606050319021b1f0605010e061204050a0f08030109140c0313023105011403030415120e010e0d0905100e03030705030c 65
    0xc100100414a10500d0b0040000b180036010401d04400800d50001d900c00300041e8042c01c0400408050300842c1c9540300611400703c2644080b005030508105985090100c140caa8100b194203000596001c41003400c1c3c0300501c1c11405a0350068801d008200c20100240d011440206d45401c000d40c0201910b80c204545001001c0c0c0a405001d018002c00c0c241400c0191101c80450080e201d140300044514000744007003420400c042c0004451a40c105200120326401801c0200d059403081c4102082d8034904505c0450340184074120300e1060b09034101490450f90341c441e010000c02c1d80800200d03844050241115003551303d4112601407001501c00c0001e4080c20300e40b07160100c40d010b0700440c0d5013600c1100c81c02d800e40d50000458064405da0754052140d0b90310584299107000c0c412208a64880c01c22000000c4020154401460068a0001c807079890030401000d48280c0c030240a2541c1082a00003040d10803400758001208000015040342d20381851a1681419038001d02008582c0d45c003d41d6540c070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 547731870 1250 547730620 547730641
    0x1030b030d0504050111010b0d0302031b01050408070b092802090906100b130504090b0f3405130305011e0606090e0405150403180e01030c05061c090308 67
    0x200001000d40082094161101014015010360720030213040020306118816054000c0d08111080300014207100114642450081d4580d001120707d00f0f0160080c8001606043d014003800b8051030f0049a0603150100d5910341032030510300240307035180c0744c440d03020805002044441360003520200f5200c0701014000c0c81c410400301d03c074064804003681c4d2254060003100e11040b101c41045414124019030b80f80c0d40caa00400c4c020b4816840242e206103402010310500c0819038141d407041d42c100e16440c000f81e4071440c3c0401d8a0308420156040450181c2588507804603540108110f20b40074107025040c1740d0b4240ca8195100e80325041111071381d454000d10800d00e20700000c1038401c405064010b002140c00c0c9003005200080d030307114581c060f56103000882c0134488107000ba040d80c020b65402c1c0d03205a1406050141071400c10034101c4282c140c1c01100000d40c264281d480c241600c0d4068101c078a005c0c83e01c0108160f40c2c100403041c00440e00d03038000809040c3d101b03200b98404a44a9101d010192900d0060360 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 547733120 1250 547731870 547731881
    0x70e030115091a0a0b0316111005070806030109050c130609020d09020301050f0910051815010f150806150c06040c09050708010302100f02011d0705030c03071805040615030305090103 80
    0x40340911110807041c417003400d5203000d40f40e0120604007000d07484010030600f104c0755106001c40442e18041c1c0d086d42960800c0726000241f042a0703588442a4a032103060a01d800c03204e4880000d421070700000b2a0240510707109204030003095801001003001511201c0f200c080f640031098004800d136440d074544d0304601b420701516a002403000c0b21041a481c0a101075501e4850b08001c00d551656144000703a4082c5010282c000f054036040d0442c4d00703044002c41107052120084c00b44007030f0158445000641c0c025071611110201600d40c0e90404551200c0080c00b13245001c1094448525600740250411814200315051299020b003003031104003071501901c08101c170300280614003006080e10050015865004596080ac2043d140034004401c0380e81c4e04a004002c9041060381f100c000d45154560300500103881d0064580c00c070182c070691282441055540da545120b002e803000e400748184080c00c000d03580010b51050041401190600880e62101e062180941048000c60300c0450b0301302140d613051082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 547734370 1250 547733120 547733171
    0x605010507020d080903192a050a032d0302061009050c0f0702011106130203100203070f080a0207060c050a030516080a11090a08070302091e070e03011509 68
    0x4a890700e403503a000310720000b14009018114030710001d6009444d4408129a4003000c084121290034680e1a1034454041c0340e0102081c401030300340540381c01e0241e1003800315004503000140340c805464690360b0703040200c901c409954000c01f0451194080c01030000c11240019510a9025000904e13002d40000c03203840c4141c1200800c18644010001d169000e081180c0c407881400c41490745650300c510040b251481c6d1310b103075240ca601800050000301d03400d004420a0040c8201c003644c01c5803585501c40801c03800211811b600003410a5810480755000c4c0300750351341103000d0782000340c94640d05407642ca0554100c0c50f40400001e42c0000c02d5071995905104d2540c004194036015225501004001031100c003000d01000315042d580c2c0d0694082c0c01140e011145031810103032080784c90a5072034030040d849600620069003c1e0b160320300010010030f8504403107190030881c10b1655290b511404421204581e101c4540d83d0550340e1354480340303203041760342c00c2c6000240800d91011841001e00188040402c031001d60 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 547735620 1250 547734370 547734377
    0xa05010510230603091929160e060708070b0109060501020a0b15220c0f0203031003030c0c170c030d0f080103080306060f03070c11010c08091e031609060501 69
    0xc51201c401907420054400290441e8429160740b07444281c14288809040c001c41c4020b4404400350821101900d206032847c00c48a00e035840c40c2510904041403082240c104081045289031520040d01811210004c1c2c01d002c0c1169040581980d0745c2000b9500600007070b902e5854000042205008500030030000d40030a10107000e20104a90326203004100180041000070941d07000d500140e03c0d11800d1008544104504c08040700304034812600401c0c20103c950002103d4160140b40c1e1400042100e008040301c1e099149501c0ca1914225551603008000f29105548403800103086007000303108012040902c8003422298101d00c00b010702c1c00a14051141c10308c20240101403085800c07440d000d0440c6d42140e0402d90f2960740c0d5000a01074491b072140b400c1c680d40c000c014840c8440d4803140311300e0100d208044000c0741d05d003d50010346461880325030080c0403a904001c0d070b0803c0c0c10400a034041603203d200d13000360622118000207050000214a86160303402c001d0301040254814010900148402e08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 547736870 1250 547735620 547735649
    0x3020a050a0e18010b130905060a020408070e0403050918160206010b0d0e010b060a2712030f1106090a0201031b020a03050a0903020607110405090601082d0a05010510 73
    0x140b22216403500140f9003a01c0c80c0c0040041c184640c002c0d086810074443c001c000e00282d100b50007818006200d84a0207503640d04c07a0600040388540c003482201d0035540b031035004082c1e01d0300e40391300304600950042c801c404010742801502429100e00000002d003049550b90100e01d450096522140040c0700c601100c115400000100b028004075812100020300754178020031500701e21100c42d40907140c1d0412080d005000001c0b0381410980c054100060501c00d40703011801c907004800d124180d10000c2c0241c1e00c01c2c00ca40b4000070000b90007101e0400d0310585c076062140c40f49406514150822008680800f07040e04040703884421580c3c144a017080704903418401182c01f04058900039500c004014000b014401e0008501846034000c4807040001d6034024486035a80704540b41c0440700a9030f1541c2c260045040c0750100765945d20108803107069030403040081101a14403107800100c4100e4484001a0009168800c003280c0d0050011000c841c0c050070001c41e03141000000101c803450107074000490300c00c091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 547738120 1250 547736870 547736879
    0x19061a04091e0f08030103051609091e060e01090804080f0a0b060904020a0807080d140702030a060b1309050a050c0d030503060613270609060311041d031303020a050a 73
    0x900034070305400b50042c00c1c075101c034501c0e000030050302020010303085140101c00002003190010b5251035801d5500525440307150b546055105440c0c0311100140b81c00040940440965a090202c03045240140c02c041000d440000001f401c64814120aa0703c41d48001010b00c42042d08004141d50070a410005258804281d01c80010004002d400144a40100008601035559140540000c3c09112059901056666000959031b440e10060702c0007040105404101608164098603022074000e40a071910701415507c0400410148044503070100081c0d0103412450054442c00c8c030742610480c01402005000c0c10018601101c3d4840303079104018007002d400c00246e2020a5940058003918401d131200c4007102c40c141d2006064002079400046080c5024003183d241c8015406040f00810404c000b0742c40d22a940b09a03a5240409030441540c01c100b05030b2400c140e030060810145210344080d01c1d1491040c1682190700118807a00304030310703010061003940b1301041140020142161841a12840c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 547739370 1250 547738120 547738133
    0x9390e010e0f040905010e030c06010f050d030e010e041107030306030213111c060302040924050709030809030a0606030f0b0a05010302010c080306030124061218021219061a0409 78
    0x2c03529440c01580c13101d5001c02001405d4000740403601c0700078107890b1940900c1402c181c3d640d500b44544901c00351285000622801c105001c2620550190f60b0003000d1280c80c401565065182600303190042da40e04441c900500940c000743c60700d28480d1fa0080b400618600403c90004100d841003c0382ea0316240d80c18420001784001c44144240030241c5880d107a56104800c2d008085552002e508981484034030000c028020007415070340070541148100800c82d1250072000c882044036140003081d0009001c2c00480c141c1000b41409000040031503004030700c56654501980c00310b500c22140301804030703c0d08041040848225900c08000310b005c1286614540000308002400d000180c511300300000819455102904401386440d403504100da072044d004224030302030f070499100314030019910400c5050544a64050b00a0410b0746c0c9032a041d05042c1e68007048607401000075000c3d001c0c454000d14264160404482c2003100b40030300c00005000c219410448407440d80d200c4241d10441c0340c401e440300010503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 547740620 1250 547739370 547739389
    0x1211150a030e0c101d0312220602060117031312050d020109051e0109061d0c010e06091002030d0908040e06062802070e0a091a0405030409390e010e 65
    0x161034040c04c1146410700100c502d17818102a113130075001e030f40c0001d441e417030100780100090340030004603200789a100d4074203165411881c0200401a0010001007002c056688481182501c105c001d903440c0c60b0446c642034035040d405900ca042c2e00e07488020080248003003071080b42c8c03400900303000a1040c5641d964501c1e845130840d49074a00d003005503401e050354513074096104a148035031003c4104001c0701651b00d507220070032580621490f90710030320944002d41d5104001ea80000080548094100441030381003200d804410800704003144003c0c014409250000d000f01c8a8082c01030540907a102c1c10403005078140e010081880d40a103004002440a0390074108848071803100030000d01020802602c0d01301e04124041d48004858160b4900f4400350f55007583c0b00441281c402c4201c04414894065010407010040301c000c1e00b42e400a120070401c0035416000324003107008613030013001d00c010065500381c0d48480031403d01e4400084841d40350340709900300e0b12000300210300342460051180f4000004d404e811 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 547741870 1250 547740620 547740649
    0xf030f0a0f12050f0f09011a0d0f1e06110909180705031519090210050304020a0f0303031d0309060702150702210d080708011211150a030e0c 62
    0x1100c1c0140380c150762203069500e005203034041c0184810b003440700080f2059841640c0e4550b071503040001140c03002c80140b203901c0c0800c401c03164804642c20050204083c25074070760310903a0010801d0342000e00281e01c0402c40d01014020032a0800d5600541c03c0800490b8040e9000000314001084211226130700c1c1f4004550140c2540c0c1c1401aa16180c08400d00300202a8001070301481158400010500c400b002c1d075115803184e901120920030001200030580d0381a0002035049452011400c0001d0b1241c1c00031540140043c0588045c0d40c0d9803d0502209081c40d8800d400003640c0700558805001204400034070101c11100450a008031140000d416125141c0020f1140401203101415401c4e0441902d6000d0740050441c100301160001c20120400031101d45102401501400507056001d00c0110740180d2880d91050f80e00d030708103d00d040707080320395500c02e45904224088120783d5540d03090030402e40c819000480d60b1680001c002c09800c0d541c0412001010340c00042c091441c640340c1a07000750042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 547743120 1250 547741870 547741877
    0x30b19060903050c030d170604060f090209041a06040b1305100e09101401320703020f0d09030206090616082a1c11010f020901081f0303260103060606020f030f0a 71
    0xf6281d100010300144ad40f43d11032046512017440000c4c0701c241d070f640038011940080c8c8090099052891031820041d110b002e800343d00c42428001401101c40e0f1101500191801c400c0c1441d845458900040c0f040c1011000b0100050b010b0b400c0e002c56040c100174581e0409114649001c519003001c225810000074000050304110320410301c0010340740726846030300000c4002c0d8510074011210340b0072014264071001054025109003480ba03482c08000103401000440680e0b18490f00e42d042d6400c102003075116103103241c2d001c0001d02040354000c8903550804a8180304000d600c4d980c4130401200c6003500400c550100c42800154501c3d220a40702140b41c05401045201c894285c251050098481c82d40b02502c03c44258602000014180312581c000d2603c2c07030090300d861045640e91070001c840c41c1d2200e4100c6440c01900641040064007034042c2e80c000002a44490781c112107002d6a400065000760700950700039843e40d8003040b8154061004021201555010b14600003501814185910680e140309081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 547744370 1250 547743120 547743167
    0x31b03090706080a15030b04060e0303090303130602040914010512010c0e042f033103080604020f070b011703130e06060d0501150e100f030b19060903050c030d 70
    0x80b02d00c4c2e07a001d444092a03540720ba00f4615140e00f889200f81d50111021125640382840c00003100b40c001080d648500c40c440000c510f1580c40c40803620b40038001c00c404494281d000d00c0003064100c1c442c001d0400b00c0030102c09800c41585802c003085504012511001400c0c2d14045200c0c10969001c0f0b03481c82e42c1a41902c0c045070608182580000c0c50810560b040000b50411060301c8002c29000300960084004112603200c60400c944400040e0301d804076074500003003418220307900013401000700a9121170000c10060510000e074400ad4025170001200b102c0710340c603140c0140502078558000f600d0400c0c1e124019030034035000e900000301c802414002e002080c40f00d08002985070307440302c0490f0b001288205d005c0c0f0895030f45800e1107080043c0002000d01084075000c129455060030182d502e0323840c0b0255203416040811707403404c0c3c004056041c0c4480d0040507510300400130004d030101307a900600b216560943c841e8514200182082c0d503440c4540c0c13203504019501e40c49150310003200610307201e1160300540b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 547745620 1250 547744370 547744381
    0x20607110a03051f060b030109051902040b220b0f0304080405040f0905300c0c03070f0e0c03040b0105061602030703030f0e06130e19050c031b0309070608 68
    0x690002465403554400c84442002c82000b00101c0c0307080840310360410005050003950051419202d0501400e49010010310041000301c80c142c000607044800700a4283c07010700d240d100801644c0c06604280c43c903004c0090b142c02c84000501d07420340c0032808843c810344442e082840351140c621070071126960b41074003c03012a051088010490303004090040c400c02030240b4070602c46004d400d45000984003030082c0c07001004900840300894190030402441d249c0d01c1d1341c40031030300b0819800070440035138148103a6070780c000e15403000c2100342c1c00303003000b084062074641c905418071144400041040b01c036100c0c18014000000c000241c12415224202d03201030b25003010001d620004c0000300d01c081d515215144000041c0744e080340071800c22041669440c2e42c21465402445028810a8000415641c881804121031204086602d40201c0644400e00e54075075110055010f440056482910b0950004140440781a070819200550748000801c00d0940c0b908c500b9180c0c40710010f00c248014841004c00060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 547746870 1250 547745620 547745633
    0x1506030c140304210c02030a03050d060f1805010b04291c1a0607050c090606120109050702160506030a2d060302090603010e0a03050f1c0504060c0f020307020607 71
    0x35484500001c070142c881c50315080c00724480c1c03811340b24881c40c24034100d0394501d001d100b80c0720030354240c1e0054010200d4003c41d98044501d940584801e4a2055441c0804101240d02c28010030052a05840500c29889141085030880348103034000072000c0d00030801004080d0305c68a1111682d00e14013414007143c034101201402a1180402d50203201605c01181c1d07107640328a510244507440034200424140c4500014002d00d8030501502404d9a805800d4050321494114800356010501410f143d0038000103001c1c668100c203082e00000e610303549030b03010042d14a50400145e0b200101c40d2403201d295503e0a004510280f00c0503060101c05500c494100088000c0d03550858481843c007060300740c0c0890640700d130400138801070004038840c000840208103107260501606840b03a0690020304020181e44d40c00342d0b83c2c0d900c002030403500c10100740202500040b01001907042110010000715072440c1034a01007003180c00d20f095600901503c56001c1402c50360000039030742c0c02903040d036495aa4019904100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 547748120 1250 547746870 547746887
    0x50a090c030b15061605011b1407061803091703032511030d20030108030a050c0a050303100303021507050a0c03140d061e0302183409091506030c 64
    0x140d0480c070300003045402004170803c0c100f19a80108020481c00d0420b02800007440003004440c000591b40f1114003034101d8040c03000304511031081c40001025404010320166110204000b50081610801d04101640ba0982035455080d22000a07514501d0000d40700d103181032a1400c0c2e0150300e025010515101409003980a04c511200011a62154440202c14000d08070540d07070750340e80405500b900d40212082406032410703900c1c5036010794100010702404581c030b50850603241425201e0101c010004c100c060006602450f094a01d40b01198150301740030b4684840c1840350030200e2001010000b070141e00c001030707500e4644a441c080d0116004d0b81405c844086000c5000403001c0300c0041c200310301381c0c030950184040351030941040046881d00903556826030306034480a074102e03504d0164602c5607405126000e80c071828220034601d08541c114201d20200c0a03903400c203521700354200007501c1000c0d0020185001846041c8040c0406c000c500d001034141c10b124440d04082c592100c40091441c1d000d0500e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 547749370 1250 547748120 547748161
    0xa0312090201020f101e020403050705091306050901020702040b010e09150d08120f1f0902070c030b0711060c0a0c0b0601020f030d0609060e0106080f04050705030a0b0901050a090c030b 81
    0x8803005401c100030703085c0040c00c845a900c049030101490404450486000f40ca048a4005000c0c1100c1e40ca410240901003800401c3d800504501032220400680d051256a010b112880001030b250009441444104d4510031000380c1485042031408099076100c00b21207a000c80304000c070070030030100b510109810b03018480c40101420408529150004034241d1031904c102ca003084040070b19100c4c454261000d0b1a00408205c090100082c14419a0300c107070000c148062244640c42e60b90b5682c2e0b2503030f40c001d8006440000000380211184015003d08106180d0084403002140c2c0c60113054060181074000c0c48403004054071030000016040341c1c0248041c455240031042503c0d0340ea45d81c003200d071006091600622800514207040451068021800941a21810f40b5040480c3d164024840c9203580010300480346c0d8481c00701c011400391400c1c040c1e41c1043d0310030b84250660341460800203096540080400c8146841c1409a00101c2d019102c03900403203802000e008280e0f240c401c030010004040280 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 547750620 1250 547749370 547749373
    0x90c07020d02010519050d060608070c0b070c02060403111e210a02060a0c031209150504050c100306170c090103080c01020c07030b07081b09040c0324170a0312090201020f 75
    0x20980d8086e8002000b4842882011010404580c485d4029941c044003a540c0703200046072070380200b0000e2006800c55402400c0740c149920709000310341c0003801035031007500308480e421040c510214190500f05216803911721440b00d0801d003c1d6401c0d010524102c10b8259040c100103964100107100300f000d11081080c20307009031803641e0f6144c2030030300588250a24001180007480030308100702c0c1200240b10314000b282c2d0103031600700220809030281014080103801681e0314001d002c000c1101d9920340c0282004120a502c020036090300d4540e65000b4550718a00d03280b01a0401004401260b5824070518107403640480407a880c2c100d01002c5e1030080c0104508900c40b031150405c04010320a910105510840f0603030380e104903a030782c0c0f283c9900750001e480215401c0c0341760501158003540ba003900003500c555030a190008110b400d444402c0e4540740108406181d130504541c080c020000700c2421902c100ca00040280341d0b1071495600140b41341c81c200541074810b80d40d115007a0441e0710911031048401000e80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 547751870 1250 547750620 547750657
    0x602030f04020918060411060912070f0807031a1801020307200a12050d020c0105190e031801050706020c0607110106090c0206041b0b070f030905090c07020d020105 72
    0x11030000400000d580c10791182c1111000100d00422881c1010000c5040c60003428080d140e40d03a07140207100354140300755400803040c00400079a48131480d5074a0309801c400e0050107200d181a0750300140c200503400080641c6c00616003031002c1004440e030783d01e0035100c200401c0007580d6848004060511207140003045540000203110200350702000d001d40c0c1e600380c0120103031180c200780c409650751329190b00c00411080c080120b910556000c0c001800c1030340d00000c405403821202109403800c45208440c01ca2140001301070051801805211703200e40940c3c40030041d440c01c09103518801001040d64080d40c10803400280c600c0c10071101da016075040120400480d07001342028600035100314040040000c440d846e1020000f2a00d0b074a014103680c0d91280e030060186a215500e41c80909014288141c034000c04114000528488a80c020009140208407101000001c2d01d00189000d505a02c0b0622481c01c40f018800400819400c54000b141e0444203c841c0381c5540c801078a06003c0c48900384001094072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 547753120 1250 547751870 547751881
    0x432100f1205071d070c05031902010509061e010e0a060504020a020d0e0301060f06260c130e01140d03020f2a06030903190212031e18030a050d0603060203 68
    0x1109032a601e02c0c8030714160340d14142c8503070b180300306203c00042d641e04481c0c551020a8845024184c2802c4030313402401640e14081e440040d0b14070005901e440d41c40180c0d0741e081044201e02091040940081c0030b000100c20405107100ca0801d9000e06000d0100c030307403202e0000f00300048056807100c3d00805020340b040d034071824500806500c6a8201c03c3ca0000300d440f0f100f15048914040c030440003540d8440c80341141c03550910340115442036800400130348d400341c0241e1900045071041d01240c4280c150002096a40240c074040d641724594641c8140066851a001408085441d6040c00708441b4250385400c0c8000f100d00f8102d19244c008030706e81c8554003840140c005a0302c0546200103a0f0781440650110100c5070006100c002e01c005c48109150341c00510011501ca00d03542e0070020b1400052040342d56890305554080300503413066910340820645045400390031500140e129a200d001d08042c10110200856025102d00c11010b0704410040009440500c00311160710400c00356407c190b08544903e0403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 547754370 1250 547753120 547753139
    0x140421020c0d031d030c090a090807060612031d150705150115032d0b06040b0a050306040c0c0c03060c090b0301030f0303050108281514060432100f 65
    0x20310f0b413030360600d8050541c2a801e03420002816541c16102400d008040c2c2e682d000c4010040c01d04c0c020898003402c0800080b00800c800c0d0203480007500a451118111541c14034014110302e2811424a001904644002d0a20b54400714a4210031904800c211f41e40c1d081c9141590826208801940070800400004229034504c000103036a410880e07102080002007940020020411521401740340d1412100203030b000e10700342d03008084a1440a010307641020b4488030f25150781c1c0c200729401c000095010081041da49428042c0c06440c0485040100c1c480055884200e561481c030f010281c9126101d4a044200c2d03441a04200c004100c0d006545803a540c50740303807452004400d40c4041c0c0000e41010300100f6925070204145044840000d0200d00031080c0000207011840c682c001a201c096901c2554820b50140c0c0c010743d08584c46803400320030145401d1041204803030040080c0a001507400071030084200b001e005560708545000c4003a045a924400e22040e1080d03190040713483c4090280300026840d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 547755620 1250 547754370 547754387
    0xb0a0e03030c1612050c061308330403080a0c11010e0729040612060e0c030901150b0a03021b0313030309050607021c0302150c04030303140421020c0d03 67
    0x840c100c84419540e1320841040e1030848104c01901a0b0441510600e0b180340050090034030400005402030150342d122480740c1403aa0514061404001304100d015014101d116205180180b22036501240d00742510010f11540b801041d00310b229644044103030549028099140944200c000280000c5104603821500c03003e05205026264203038414100c05d015903c40501c0e8200c114800c107038100340c0b501c142161182201e8002001c45682c0f44400b0901080800403548644452030511740c2d40e04003140c1250848a102400160030b000e03510301031041003903c10845202c1d140702d04e00981c40e010b1038884541d0240c3c52003100300c25480001030140303210340284402c40c1207034040d880e00701e45a981c80c8180106442110340080d845159418400389a580485410840c64003910444507405007140c2c1e035802110049c1c52080b1040e03808101041010b40c18010682d44c16200944031405040c0b40ea2941c0d00c0c9000110040c44a00c01e46554a03640c9100b0462242210301c003c004282d490360310704003c0c0000760b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 547756870 1250 547755620 547755643
    0x30303090d140304030c15060305070b0a200723030d020114070807050a1d091504150f142b02010e0906011e020109020604090f0c09030503040b0a0e03030c 68
    0x14541c00810200b022008241c034456605502d52000101041d5a400035220f420000c100503140c2e60000400420340c00c104070805000d5004e400b0355146108800900342c01200111030b1100c1520081d402d42e21540410143d0884e0b1b0000c50745d1100001c60401008856864143e10390144180c400200e9103642c1500403805256000000415580b01d64804407a07508049404038007081d42041440c5000d0b20848481701000c0e4000314100c2c16204105c0010701540c002e0310b180c148a01402d000c40741e14032301071007a520b1031a0900d80a030103051a121f061051003089d482a41d4001c85501d00704c0742c66032200210316840c62000c01081d010180004000d100110065200ba80052201c01c04031110341007030304c01603019900507141c401202e195000100c05002ca40c0114000315505d4031054401a1123420141010b01a40351010684032156604401110b030700402001c20001040b00c02c00100301c0200454068400801d040c41e0340d0b52428006882c100c0912102c107030035100000b25000703e814049412030000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 547758120 1250 547756870 547756877
    0xf01060311030103081e07021e120c090604090303140c04030b0a0e2d161d04020a0e04020609090112060507050c072304090302031308073002030303090d 67
    0x11007180400c0304240030902000340503136402c102c00401095010412500030b001d9408052604c4081e901141080709484c200342c4036804940705064203840d0221201c000c42030b407400100340c030107d0000002c00e4000b018152b64011361383e41149105052003500800c01050310000310080504214074003000581c0244801e0790b8001d00030700800d00210041c06260b400c3c40001c40140000c4259044d07500d90300c80500c0b9050814858120351140c9004203020584e012144d000d800d40d40e00c1d1401000602c40c00070004200c45202c00c07441007100507a0b400c01c00310305880103018885c06a41e21440840d41030300c00d030b0021650041307003040000769030035516515000d4184101810b0140780c881102c1076a1030300402184541c1e0b80c000030018070503402e0181c400702c448100c5241d4031a6040c00303140410129000444150b006800002d040030031200b0740e80c0c00e81d000341110b00041c00c8880c40d00021031120355090000c40881d000c03c8400c00c8805040c188401000364008098039920f061001c58190b841320780c031203c107002c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 547759370 1250 547758120 547758131
    0x108070315060f0501110114010605211b07030e041b020d02010b06030a092102012316052d0913021c020708070f24020a021c03090206030f010603 64
    0x2400014028201200d0070301583c49211070800340152001c902c4102c0480c4c4644d61401c1034440f0ba90118030307060017031206c2e46400c0d5039501c40e503100089504001c3d00e10340700306900d1014012142c0301c18a5142920b01c101c54601e0702d56060386021203803060304800711680325050140007105c401c3e01c402c90388840001a000c580f0311440810059099441da0511a0740c002000d100040d2099041c1d00500c4913a07120b00c2c00102c18820341c902010f54205200d001d800141e5440c80340003180c020700e14200c11402401c14418600e494000c040001070300c0e40300001c2e0304000000c56521130f040d002000c0c1c16408030118981d100c47c12024101c00440e50080c0301d0481c40b40c82800269000d2000c10300c203c91744040f10054083c03c061303507030154001941c4000e1040b00d100031b08211030808100d4044000d8502481041c03408207588040303049100704480d22031031040a03841002003001094000800c1400300c511034220324804d80741c03048154002d040307503503000e500b00c4400810044101d8000100a050742c03090b40b000c200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 547760620 1250 547759370 547759403
    0x31e090406060e03060402010e18150a0b160807030c051507020606191505280806040507020d0c082205040f0e030304410607080907270501080703 64
    0x201d90004030f0046806420080100380554410f8480c01089180902070030900c071240144800c840740126102c02844c03e4040f600c0752a49008071400000f020301d481e080c0d00f40f1444011240b0742150450006041ca08000b81240405007d500c04c2442650024140c03250307101001804204110203c441d1001030041000150791071034021142010009403801003100340342042c2d078140f5800b4803c030040f001c1c0b0000307000300c0040100701082102c0f480c1d09810714181108400314068a840c2d00605010b1003030341448100400704da070005408120000300d00d4883c4080303030241004c4155100d00030740c10707007996078031550a070400b1113008003402242c0c0300341c80401c03503041c8003840d01d000c03030b00d2400d20042142c1041010a002c41d070685052400e0031200c002d042c105040c0022020000b02142110454591170500030504d00071041c0107040c0d01101c2c60501d40c040e0301d4482d1a950300c4410a0084084070300180300045100620490760080c0300e82d46200811007541c460000d00e036621a01c0c4021200c03295035146144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 547761870 1250 547760620 547760627
    0x6030408120a0501060f142a01050108010c050d09140d020f07080307080a0518040f0f0b010e0303030a0f09020a33090e042405100e04080f0903031e09040606 69
    0x5040310750075a0391824068628508a4042032040390031440e5850600103041c0d0003000d45490b60801e12003103600c108c0c0c40042d844044c00c0d11016481040e00e1b0345001c1d42103d4050b04402213a035040801100041e4202051034545030b8000603840000c00340c402c24210f03900030b6400280c444442e4444104540c50b01d40c5d101c03001640c034403503102d000b81007038828404080098041c8011788850021701e02d00074042e0500d100490103c6411412249100b51510078030340e11031901c1d1048150f00c040a21b005052007041d40e001c00e50b81e201c09030400e10151f6a0305400841340380c050b070044803c20343c020980010f07070340e0740c2c2d072a0383d44401080302c030640403280ca50588409050386010507060561548074010000d03d0103403000c1608000030000d50310001c10316140312441035120415003040c20b030704800240506080c0d05041c5a2500c0d6000b404102080409204c0070070880410394000150f9407402503034502946010a04500441c440c061003403c2d10325040501290f50b00141c00000015a410020750369103607003c0b17 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 547763120 1250 547761870 547761881
    0x30e10061d01050f10021c1e030c0c02010e0102150a0510120f0b1305151501030204120206030a060315020306040b010507030f0f2307020a1203050a081506030408120a 73
    0x10754884e40c10301c404862400c15049003040c0191600507148080d00304140302403007001288010000400c0081c06283c11034640c01c0c0c9035071740c2c03602d86000c12140805a5015264008510000e818403103500c202d00401ea10070007e81107080d0303030700e44401020706055041e94068031040e50a401c1c10718181e50081213107804280040072554010b10384040000b0b054444807900907001d800002c50307103480804080400c108120340040b0300781c004151211482d150a02d001d4050070300e0b03207940c1058010001088400b81401351464507580403550240d69482d890024002407016602c0107140100c400d8800044d0000d950186101c1d510030b4405000ea01c110800444051003900001404299805080c4100724490380703a88410348960b0900096801c0e120104d903400340100345c4040d00802001610000318101541c0840c0184803400c41e0300018012a580a011801a94007101c100020400042c1101d038182240b8003034a40040c00890b80c90410b400e00c5249a4004812140f2145040021400582c0b003403048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 547764370 1250 547763120 547763129
    0x90906010f090b0d020412050a140f070e0603031e03090105011d0a050a1104140f1e09040503160c05091003020a170a0605070e12011e0c030e10061d01 66
    0x40750720b06800d00300303000d0682c3c1045900b0900b0590901000c2081d12036003c1040c5206d000f0340040c08005501c0c034004020884d4440c14071a550052040210828400a60801620311203180b05141d60384000100b4514010b818800c084500c180320415805000c2d14029400703200f211000740056a2200c1501d50200040303085124101d42c2d2030001030840c107650784142c2c3c01600035407002c0b50b05681c0b982044003581107074014255119429032482c100f898130b0f09080d00394100c141c44131440c1000d03003d1400f664a19190006005180321030005003001410302c21521a41c00c2d10b440744901201600701803510b0300e03c60007503034054807440e80801c84542003071100c281100d0780181548515400d10103600b04003102c0b0031b40c4d6141480b50100781c80001c1c185001e0ba0348588903030383d00c184d080803c000401003c00d003510380309547c2d44d00d01189213001c408884205078610203040310108075504126003c070010041400e0010305401000340c245d8041c2584d410080444101903030a40040310801d00405001000388035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 547765620 1250 547764370 547764377
    0x2010504050a0b130b041209140a030204090804091119020309090105040b04020405041b0305070c0b06010c0819090602241503030405061605010507110a0f080c0d05090906010f 77
    0x1500002041d43e08800c0d807100f20070401122101c0740350764060342c005055a00300c3d41c01c1800030914a4041e48284c00b580200020a00b0032504041031011035100d82c428000640641d4803542d10320240445030040300c0003862444001c02184042000f2040701d034000c00032040302004103401c0c801c0c482d4800800c0c0c90a454009000c000d0a920340b80801c00280404402d664002e902440f0002d841d03035491149842c0d12070541f8030044281c203001c5000b001c0701d60041003d014480d403d010a4040760200a06592000084c00e001101e89014100144039000c1c0b04584411100f844030301000d41035100b220705080314060313002c8945400300800c00c5006a440d000d004010415010001584d071030400a016030700301e0014bc103680c0340640700c2021035050741c440030403148030b030144107001c80400c0340900c901070f8800324030703d80980707802c42c500c041949484800c540500260310003038410040c084810115580003146000316090b0007076000c0007800d075800030744a0f0b51155200c50001141e650140c1c0038480849030715035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 547766870 1250 547765620 547765633
    0x2060a050601030f0c02030c15160318061d060615090d0609050703030f090e01120308041a1603051f0b0a0504030605040804080c030d0203030c1e0301120c060201050405 74
    0x4024400802000301124100364582468004004c1c0707503c11070403901010390255035103c0e420300c0207900d04501341000c810f00740d9000c8100020a102e101e040388850702c403813502080203000c07915085c1100103c50750280c001803402d25607003030710303090f1110003526640c1d11001e44869995400800c8480d03008511301c07201c10401089010510700e4031a0b243d480503449640000b506090940f5a0b03403524006400440104103100c0d200c0b130003107411500c420024981d80d5400d081940c10880f0700d614000b55040020180200300d404101001100381c0c802c64181000c104980b800d00e40b003114005480e04112074203000c2881c1c41e01013110780407031034000380800300800340042d08546003660f03d44041c0e00000300101040700c21306c004400116540a0329000d02c4c0a844078030740761420200043c1c1040c000b004487c0c40703035000802c200c91240c0c011003500d80c400400000e003600c4ae0001d11400301c0825000303500c801c903203d0010000c01c4944c500c40c0300c000d0040c090f07114460050340301d400907400c072441590b001e0700c294400b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 547768120 1250 547766870 547766881
    0x160807031401090c05042411010911060306220203011703190507050f071806050f01090905090f010618051b030105090c0d0c0c110d150f021905040609150206 69
    0x4d4204481c441010300e040c80c41c1550fa48005155101000d00350403402c3d0f10f0540004c203040c1d101e10010722074005800200903a03c2541d80d000c0e4030920600381503001d11004400a902991049885a0508104010702c0135603d50030407414000e600902400798100643c21444040090000c140d9900c0303200002c2c1840e240400c0601565240c00c0244111903c0c45120014801401c0030b0000c48000c00c0d81c0804001600c42110751300e0252541900b015000d0000700c0d030804102c0ea4071001000485143c8600000d040d110061001d0902000c0c00c8554600e6090007400107200c0f008920b0100e82c401c03820004c01c050b454500c1e045890388110350091405101c2400180418988081c1d0290071441903841245008102860182035440482c84000400c00b91041c0400b4012a08155102d1a0040758151120ba6056417007580c0c4d00141461807902c40d81c1e900c400c41402d1500da040b2042c2c2001081964030141c07031460300504c6640580140700002e880a10300044603060f030f01c0c0b00c84015440350080c0011380e0350f4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 547769370 1250 547768120 547768139
    0x906040b0c010e071d070518190f0e041719030f060302040c0503070210050105031f09050a14070f050d0b0603010908040807030b0f010501021c0504050603160807031401 74
    0x1103101d00956a941010280150800604008000f1581d4054092800100c1803d00d400300908040078000c0030886241d5034006000400c2c42139074125141402e80c02e22120300721301070b0700c580c001c03d100071098280486c0c0f58100b10038440c840c6114400902d004164100c1c6840c2034010030941c80900100f01411400b0076000742c01c80e4110304078903040060070f171b41d607034000500f607900c80c54003440071400c00030601c42d280e54180208100b40410303000c00e10a951415010a903218000880c1d1030f82d6800340054080c0280403504070381c010035001400c03100d04030407a081c040320503c1803d0f032042041c800c280780041c0c485140c0038248215100200042d100c42c4558441c1c2c15202c038000d00b007a905550b01d1020500003551480500050460240117040850039403600c11860341020700388003450004800100f0450303900146090f00c0d6030580084601040c55044181c425000c3e603007006902c40c1c000f208000908480e0411f038404c0c07945136030f1954100c0d03c7c3d41100743c04441001d05117004c151989001032240028 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 547770620 1250 547769370 547769377
    0x4030302060105091b04030c080607030e0601140103020f1308100504050a1515140f0d02030a260f0d11030402092a030a020a1707120c1b05060712020906040b 69
    0x4144114030045c4664000304035070f5000781c0040355800540c01044c00b440c030003044250360100c40d50500b0030912021100460740c07142d0500c1940c0c0c198000092000d40e50b48640c05988101d0740c00c5814a4030350340c007441024415031060003581014814210019030800350360041d2801190400c02422000300c0c0c0d0303214001850403581d041a107498071b48c817007803030509030302c804c0c0400030032042118040703000c440420803003800c0b80850b03807620603c0160b10700005603501082501e036965114658214640161440000400c024001c90700c40b9400401c10020b003100000003010300f44c2c040d5208100c00c210550300b200c56400f040e100690454114000600d10f89000c100c0040a02c030011005401d40c0049919035000d544200c0f40071a034540c010a04d810100c3d040a811030300e003808e03120502d49a20f4002e0000740045601d400040d5420744038011240d4460040c520441d5100009000180701c2156051455542c0b40c19200322002900841040300109281d00c00c3e00c418200082c802481c240c9440d085020350341 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 547771870 1250 547770620 547770631
    0x50f0f1525051b0c040b06070309120507050a0e09010501060306180f0b0307141509090c070f08120906090d05220f0315060602060f070c03110d12050c0403030206010509 74
    0x8001c12101d4040d282c080410707250f90070b696008051100090f0280001d84410780021070152005001c9500025000800d842c15540c07068110041d400190600c2c500d4480716034030094120010200200b145141031181b02d2040304500c0080c0800e0342d9400d002ca0498101c1c1c070541c01889040c3c10380101100c8160060b80750120324520200e000c210210002e41445807586c482c1598642d100c401c5105410b00030400000070311000d20103400c1543c183d01091180d18010102c4244640005101d020000135070083c80161350030583c99a2944001711817850006400d89400d00c03503100d230074001049000001501400c0410b03560f0b5080c20440c00104a50848202c010005041c1528a030041101c034254400180194000c0403605601c0c0c01000014045035100e0708070b40215040f503810030054150042623141c0004803071501061030205401c0c202c5100025002041c090f0040c5000e0340c1c54141e112043c0c860071004c0a004020319100d4542c0024248100c0c8001000742e0402c000402c05403900c03420456006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 547773120 1250 547771870 547771877
    0x2211507090e160908010609090302010608070b25080403030f1707051b070e0405010b0a08060601050423040c0801060314090d0305091e06010f050d05071809050f0f1525 74
    0x13035102c0050a0075504c2070b4110072003d5540742c840e80b05065090150000074100d5101034680c0c2400e000c0d07a02450301c58400500d080c00f003030f40c001000300c05c42c140d042550a40c12188194a443c0caa140080c1642640c0d00103030005820b1901d684621060b40c4c41c0280206250f89070740303240400261400c0b0040540c40c5540f1a81e005180300006c00c02c068040e030600c140e104000020360004540c08000602d00a03810404e41760748214108403a5903003100448095907981140c880c054162117407844070382e4a12a240d00e070400d0034005021403090700b010b4102d050344d030707161414000040303405011189030300212010007066200c154812090f40c0640d201d550005000016501001c040c2440b41c03a1240c01c403180b41160782d201c5001000b20044031100c0c0c40182a04603507203400b900d25a12090707517405103070280340c403485c000b0b082e02c05d20a01103901002c022035002c1d040d29107032060840055292502a0014810703801000d61452103a2010440c4034400c688498071a0803071490356245a803440210400507050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 547774370 1250 547773120 547773137
    0x180f0f030a050601080d1d040f020f0d0f05070f120509070807150207050f010f0e040b040603150501050904080406031e05010905090d1e080402211507090e16 69
    0x2a1418801d000d40107000340001c050f6549400704840c58801804880010448040b03000e416040c240c4000444400c01190003150000c1d444080070001d20907021a10108000001d0001140c40540c005042e8400010003c100380d5542c03510944802c0c04038143c25002034114081303989104891b5101903081242203040b03903256921185010710b00f22450300409200d02e44000078403400b541c10001d0740e001d4136050b038080c1d001014410020300440004e186480902401440c08103550f01d950380302d50a112001030080c840240e83c0e00348500e0865084807220221410b05001061034202440801e0096502000f91442c0c03518000d0201d00500c54030745148002417446040b00341c44403041c02a640178140b11400002c45090281103a8a03000d00c852086050041d2507101e0302040c3c480c10715000f550462420204499926440081c501c0054111001030401d80c0c265042c0031483d0000d071800d00b48095511034121922070b08000c0c1c031003030090701ca0240700d00070346400a6410594400341c20002d201d1030801400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 547775620 1250 547774370 547774399
    0x1e070f12121b0504060f18090b0108061c0f0503042705070804020a15020708030f030108070b030112030e01110628020708030f060105071703100803180f 67
    0x525a004910000001e2100302145026641521602420042420784410541c1d00001c0c094401d0250b44110000e000c0740324402c42e48103009001000d50890b4102484085c16100c0b01444010241400010300042050b000202207081400380115018041141d4112100c2c0071f6460b80b41049018104a6880c0028003000546070a14014825003200c0c01900d02070840d215803151044034001482541009981e20611001d80c50f20701c07804050790582d801359003c41ca4401c1c0d059142880b242d0014a0900c00000c651159602c1c003005581030300c0380304040c0d4407007030781c1c9185510840c0000c0c000c004600e0b540c281c55000003402107900d40301d20031041c186000200c1e810001103007054421034201030405100f48400105c0000002400d0b100b0510312011410801c860b02c540c90b07131b800b0040104082d0560320b0301048441e80280d0a43d145a94080c50340c2c030f50821081ea908640b0b42003603810005610389a480818a2540402610100803803040803070091412201000010808085402d0308040c8120507000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 547776870 1250 547775620 547775633
    0x603010302060714011103060f0303071a0a09050303091b19050d060b04090b070f1b02100e060408030d0507090308190e0a060c0b090d0f0c0c0e180d051e070f 69
    0x114010740080d00d00b1f499140a00507c800d0031707000f008080c480e4100b0409200091404500075138404440038400d01c13140e940c981a01e006043c541d80142c0030f44004000c1120244000564070110b00200089101c1100d504083c0003046e401e0450f84000c0b076902140130f0045050200d4480089070007068040748218600011400f221020303202507403981540400c0040c00c80d000000e100010080380b070301e1288509a03105481100e40e4146000b4890340850b0044031304140700b407082680c440e4000744401d0340c444d41d444917207a683d40401c4801c2200e5080000151181f402034a0800489800c8503006240c02005c3c1d0301c074480c0d01034811920041c00341c55201052f103510307400701280242015403a11408801e02c2d04000c0599000240001116071111400000d03c561100c548002001c4605000a034280c10b4a800e0010040c10b03080440481d0f80902001000403c07103490000c411180c1068450035060365a040318107200781c1000c1c0b10302c8055840d0011014100b50001d0204038041c04000f6184555584c480c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 547778120 1250 547776870 547776881
    0x906011b080f070624061b0206070209070809010506090c040b1318020901020c060c0a03080a020c010f060513090302070506181e0a0f0602060610020a05060124030b060301030206071401 81
    0x2e44c1c9040d40c50303400c02c81c0c09014a0980d810415031452080070649822402042c46000083c174130740c180b641110b15411501c811040d1505194000e0050f5164940400014841d00046507082425803c2501245950804135140d0b402001040c5040d0b140a007480c031450030550204c0400e24001110f8107001405942e525506001880815405651406020700091500000b055820701c0b404003002a91a403510002e00c08050b154982404419546c913074820100034060700f030b1060425400d02e0558140340c280743c0d0201003510000c99050500150b02c0d402081145d405200050140e0310a6000b40182d00c2c3c00c3c2c01908000f00d4518103810010f41c90310204001c07a031192502000010519034441c0c0307a1070055002030241076031804003c051850410020b5070b0706c40190080e4080c481a140c80055203100340803010129800c00200c501d039503580c0c2c1c4102001c0c07500d803540789442d40480114022562090043d1558201c00606480c02c40c0d003103030200903540d4800301c41182c804c00846896015920700380940d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 547779370 1250 547778120 547778123
    0x1d040b120d020f010b0105030915100e0a060e0906130611071407060905030d020c0103020a0e0d120813030e09180601141903030c141e0f010b0906011b080f07 69
    0x81c0c5a03d512101a043c00c0d00c4c00d11340740301e0520505100b0095840d4000828118101c3c0c09a5041b80c00d403120131104450140c1038002140d0f0781c1c1003408110458209400039404c841c107803145941c880c0e81c4d01010310f45440d81a0341080c100c030540c10062003c40c845420042d010b4004010891030102243c1c2c0e218140b403162901000e250300011170800c106908208014000c000940103800e40c80200702009444040403002c140c14147c1c0481c15804691140d45505aa140060000c1c840302002e030614a03407855900843c1400514600b001030045030307100c130074105842e626454410391168107100300404620028840702140c0c40e85c1c40400985082040002e00a000d003084c8e403040c1024140a1028098030741505002d618107086080001aa0020004401d03d401c803e404841410780844079040c50382042c405203a102c0d8065070701f241e02101007940d032070400702e000013000f80c1c81c4a041444904a02200c40ca4049081180c48180b20402a19104031040c0701e162000d1a160750074284200707a0b00442070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 547780620 1250 547779370 547779373
    0x1090e0606040b1c1130030708030f0712060305030304110a12081e041212051207050a020c04020310060806041103040b133207150e0307080d08161d040b120d02 70
    0x4846d10500b40501d140441c1859400140d45401c0940d16140414400501150b2211401400041081c0e20030300007a201a16038034018032144d55030b0304010740c0e00e0304151825600c50040022503941450080640c8044900c84840c0ca88184400e450b402c0043d00150300c000e450741d21449414160072501002080a80f0031041540c1590745181048035903004c19620340d100f403080c00c20050100e00035170044680d1100d0989001ca0795001070038000c906100101c41c03a950410300100500be1842040001c100c1911a03580d100c100a03983d40041005a8500c4909286507003030400104001c9405450896030020007d021205d14109554900c03140c0d80f600703c5a0281c0300441285030221865441c010075142c0c0c0d602c0300402010b4100011200290164640c080902126807001c0340141c405001c0d0f0380080800074181c80d00c2031030000b40580740c8181110103010107003c20310360810b1a4003990b45001c4482c0b07280074900c09241800d06000c0204119000e031903100c0001001c1c5d0104880c10402101c50244076130 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 547781870 1250 547780620 547780669
    0x10120c2a0f0605010b0c07090b0105090d080903010608100f0212041106070507080c0405071707110a061406010201180305092707171003150203100e01090e0606040b1c11 74
    0xa00c2c6c0c42c24025240c10040c1d12600304283c100550380e004d4295a040d80c02202d810340082020315000c0340b60f02c03d041c1b40c150107500f414400181800c011503425861080c1003000d110f407180070f2003010120303c43e0101903c84002401d0115002c600107064001010030003030101442d028050302c03014904040c07548250215403140c890204c290629010f02c1e90010302e03500305a1a0501900c852a10400c4014114801c0000180641102003c01c01022840701e0300013904202d140034080300c0c1c0010010441d082c0b40950b080010180741a41c00d902a400d2560700755890030706292081082041d01400000c82410410161101d100400c43c4001e0300c3c2e000e043d0a484a02e01003c040c0e0008440580080c100520355142860400c0450603025014008079072294006a0301d030780b51300c3c100c4101d5041e500f000401800d85000402d03a00c90325440302e040a44107800f103a880741c1e170b00c1007040107950044142a0f0016550403000e40420030740c0641703c40451050458000081100000c0f80c4100c00090b0001c00c1c000450 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 547783120 1250 547781870 547781887
    0x1c150b0a0221070f05030f0703030e0705090c04170a0b191d120327060f0c16080706060503100f05010e1510020c10120c2a0f0605010b 59
    0x108000c2c480252076000a40d10004051000300b1180030309900500ba40c0b9480314000f0802a09100301c480001d08001d42988071002810020020010511a11054415920b01050310f10300340004610500e182100c0c5442c090510000107038201148400d211385100b41e03911040002c18400103180b0551194021542c01e050018104003501c003001c46075104040d20203940b1034041404a07010318404203055050703035a0b444203100b42c2841004903a04004090f807600c40b0300c3e5402004074081c0c2c00350350700540710922905e40041e04005441405401001e40150720a20000106501c000e05a040e01a20001807800c1c0d40c1c4001c01d00704003501072400b90541c2e981001240581541c45060301410554852140d0791910702c0c0b00000b025100070009210780044003000c01202c3c0308001c005400c040140c6803500b8132644000141c42070218010800c100c50a000030900c00c00d04c00c0400c180140c2d8490504003a4a0b10030495402ea900ba4040c166004c5d14a81900b5003c145180210790080105c80ca9040da1980c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 547784370 1250 547783120 547783123
    0x51314210d0b0a0302010e0616080a050a1202120412030912110106080c090f100312020303270c09090708030403110a151d0609040920030d02031c150b0a02 68
    0x501032161090002c0f0700e0030704c0540d0780542601240c1030162041642c80c4006c503000001c80740380c020000d00c0d0300d400190072080c503940800a44181030700b540320b0104000c03c0b5021402a40106a400c0d095003030071100281c00307c3c140c4601c03502002c4040c103000850b29900d4442000040907003131085c010900100202d403646109100e180020200c2e040074041408c034800000c0c0c605140508401408040c00d4046065006440c880720020355101c2ea42c0502c0034503850f8040d480760001c6414a0030251220b1031017054038401c0d03040b000d0141041000d4602113100c081044000f403400f40c204421071041d440d01240c1890100000d0004d18094417903049040710290812805e00d900307030840c1c98910184102c8601aa40005983e400c3d10001010141c4041100c130204101c0d00400b0303611588142803040c06018011845041100e10411540c0710016030414001d1695600319255a500160700400c11904d005c040785030403203490100d1840215052004011603a00c01540340c001d5502004d0004a80040d60340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 547785620 1250 547784370 547784381
    0x20f040203040f1110081303140c070504060905040b0604050a0f0e0309100f08130f0b1503010c03050606070602070f0f03020609060601031a0f22020403020a09051314210d 75
    0x1302105c4036140d00c0c002080062544034054801d607142883c0d0a042c904140c020314000b40611140da51003034492180c03580560b40c3e42503501c9401c0c0034a20f00f11012070501100d0040512598000c0c00d040070740d45400040c4001004020300c07490030603a4a001106038609a0f0207201454001d1400451f221400b075410007243c204800020400c2c401001350840c0915080b01480340e10140c08820218490103070700b0000300d94030184c480100310000807070400c0200b091680c8408003488080e0000c000d800340ca444190f046070b4094886507807100701400070340c000a003290010321320315115440ca444403c56564580300d208902010072000b41c1c200008000d0841000c2120359030040302442c0c28000010341184880c1009010070310781d402000c8650008101b80c4503e01500551a01980c200382e45c13482e00e007030300d2000b0340090000b00d200d010424400140c0500901540c0c1c01071103010009205072040d9610000110040c0001d0700160041c0b10340103145421000154040d000301c0a11140c0d44d5203c003041804403034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 547786870 1250 547785620 547785653
    0xe0109060311180c0a0c050616021e0304120204020d02030c0a11060f0a020708090307030602040503010606022803110d2a030c03080702030d0f0b0f0603130f020f040203040f 76
    0x3900c40f24031014506500194014201580456640341035550441d0307074580580010705144981030030700c90b0716078400d0310b640d02036080c079401d03180303c56401e48185e140888000c6812120f0342c801c3c04280448144031200c240030a03c014001031400364004007400580e082241c4140c180c42d008180c50000c0c1d40c0101d500c00e400003020020380307a5484e2208400c00000300c0908059605540400c03400704000c1c0d00002c0301c40001000b4219280569285441c07000381d07119004e000e0003542440c400207000b600000707810b050100c45480d42c4031550920920f00b51034007415078050342002102070010303184400a03c6083c3c000c400c83c3d0794150049903520407204044a020094111000c10004a00d005c00d41c821019010107501d8506510b0544030150100d2450140c3c07001c1d00c006503d000300703290040105602900140000341c4120510020400030032016003c2110003000e050421940800055205402c0c03900203440104908400655200030404a0f00102d50407602118000500c40510800002c83c40551 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 547788120 1250 547786870 547786879
    0x509011d0c240301140d140606041a1507050111070809102c0a050a060302030a06050d03021002030606071406040614160c0c15090609080705010e09060103060e0109060311 75
    0x10840d000000c2c40ca44414420f01d0541d5400680402e0103566041030802440e4111501b041303504910080292a40e50a4560702e01c0385241c600003180781d903100b250000c0710ba03074010b20b2a40450341401800a0650080742e00319001d55a40030200130303202000340500903e601076a092515a003424092042000d82c0004400a00080d414043d1441c0e8140e484001500c0c911081015034146580c0811401701043e040701d5889000300b20302141169042e805144181c20fa4072040c00f182d43d442c070511018034020301c00074006030450754200b0008260740d001143c000d18080c00d40d500d440d0300d0b6280d960003858020303103400281d00104240028049140602028a00408210400e600700502003124103808920f150080c070802c0b504841c20b0000c040d1620004041154100801c000d40e22002000540640201e001240b521100400e001c4000280d5100b9500113845070013180050030200031411500405090405842c0d00001c5050901c080c1414001c203040040414100c0c11480c0054080c49a19900ca004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 547789370 1250 547788120 547788169
    0x607052218020d06050303030a0207052406060307020f0601030609200108011203140d090201020f1c03020c0c0d0c06030b040506030d03091b080c011b05060a0509011d0c 74
    0x481c241814400400d03001100060b030300c40040f0640c5015010799800b00e68180404010090824403e4000340096445441036a00100b10105035024299245040113150303499400026500e0800000131908000a40102c0b2620850301c1550b900e0480246c00403188541c450f03145c041000b00032021711b0b10340c00420505036041c60019000914420051003854111510100c40c0700905000304105446039400902090355000002e00301c40141c514407001b00e005200b41140401002400300340340491720380e08412040703040e129540c11000b039084094807403180d00072144080865601c40445440c91031203400350380100c0e460710300d014080700d115203071103401a030a08041117075641d00822080c900d240c4900f00000e0f80c81181c20a0b40c4180450750250790800d4251001041d40200003d112000c0380090380c80c0c0341440d10481c0041c3c03194030440380c0200554441d8010070000d00c1150409a44040300310000255024a449492540c0250004009071908160011113144c100b4811900c00c55802001002d076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 547790620 1250 547789370 547789379
    0xf030403061d100c0507060623060a02032703030a08090c030706020a26120f01060507020d030806361f030f0317090f100b030a0305030604090506070522 67
    0x440740c80f4110319150b110307a12000e58000a00800c103596207590814010010f50303482c0c00006210140130200040002d040503860455494064100c454500c1140d020790700b40581c80c2000c059041940015031088856003e010140d9201000030f0000b01c1c0322503441d004642005003d8509103140c0d066494001c2d04442c90512400f03800265040d0819031103054180a00103440d0500b11041301d4402291800e900026008030061500084501030043c8a101c8001c0b030340d07954421f0b82c0b90710940c04001d4205410520140100e8012030070907600c140081c3c4824000b61500d015264500d4210181c0c2d40c80c440d001c040802d000006003a060383c4219065140c02025441e440150711210003484001d014101e00b249113810540b00f40079514071645180d02907441c0d03080c10400c007500e03030400c900444448d01c101408404c00b60200d0040030001038018024140900190701c0c1110641d1005180c41c0d0001c2e00d4080110000d0720400100340b0907205039403425115070340c02c1180300001c05200001c04a00d24104030900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 547791870 1250 547790620 547790623
    0x1e070501140c01060f150e03060f0c031509070201020c011107050307140c060a120f140c210103050a0b0108070807050402090415060201060f0e010b0a0f0c050f030403061d 75
    0x107244454039540c050702c4250003031006001d00600c1e00010f02d4003001d0600011503010514180c074a540f1036460351202c4010200c203144e42d1b001c0444d20380a94001004c0810008400e00e402590040c260b406944032603402c0354086203405c24207903000001030390300143c50303025404288609400c3e818440801032504606445940c0d0300d010343c076405003900002005500e07800004000340c100304040030300896190000700320007400c03604060030000c61450810148025213503031445150201081d40003c84030f60b80790304468485a4000140740d40801c4040101e0500b003680c801e94042c020752050000380000001c51800f0b075244c201c1a4001046540030b440d00303000c0074402143c2f50055074029100140c50360500b50000300a040314000c9400244080400892510b5064012009130780900c43c0c42c00d000c503507580380110070710340c01d01c552100390100380000c201987c46a03c4001000185160409007904281c645900b4a42a2001d5121070b80c0300007410410001c09005000054403c180341c040400006810b06 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 547793120 1250 547791870 547791887
    0x30c031509010b0f100818150f0f07120209011815090b030f01030b130b1e011d04060b0103090c0e0712050f06280b0711060301050a090209030304090e1e070501 70
    0xf0040c081100b001400407c142c2e10b008a190100301c1c21a2402c0380c040f0b400550868050751801d01e842c1265000500c80c1e054040007600070901540c403090800d0032907580030001d410403204541007103c00d00d0740403514401d071600c0703001600a209080c49100e1444102a040c040c80d40d0001520b45003e00420000d80444500301d81166004000d170380040d641c07072641241015141100808082c9204c05108024400f61540700100051048952841e603c034400c1c41107203150320b005a5041000440007400044154124141341081070402048814942d55250160119500001d0002104008001c401d0743e00075154800289001020880ca00b0003800daa0f142d214024041030240c61020701d221004c43d0b02d403186031940c0d582004186021074645e41401125400107405949554070300301c2e18141c900e000030032241203034002002c0d114031501d4404000c019401c040f410a40c940407e010005e2400c407a070107814200d00710f801c0034108868a1450a484203c103400e8040d02651200b581407100d070740c110440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 547794370 1250 547793120 547793149
    0x309030709141b1e03150102030408100f0f0912080604050115200102300c1b03040504020a0302040303170402090c07020a1203050406080a0509060106050702030c031509010b0f 77
    0x5200010303a1000701e03007041c1d22500582c0310f10030100b0103520b02c13a00d0610028601403030b542d0000c0e020719240c1d0001280e0300d0240e80030321007443d00300c0721022090100302c2e030080000b205041404640200d205440c0012520380c0b84055800701e400030300750182c0d25030200711f80341c3c824070841d1700b0810341d41022040b426041004624400340500d61000b4002c55084c4154a00c0d903400880c000d541d5203070410380c0303100c0c0300c1b04501507201c140d03440e408840c0e000460012607601c180c02e001003003404d0074030000400c41c017207184030500c81807400104400b0400d501da83c0002d00e82c10301c090301c0240e9514514079004090040121404004203151801c5c00016680d0007c2c02e0b8108c901d1420003503c90005000140b0482101d5101c80710001d10281a9030070107400c50040c108890340340d1141046a55211800300c103403001160203085580228006000712800780c0081e02407a8000382c221002d5800c0703400441d160090001d0482c10031b00e0800b0801c49810424026022164029120303c00c02e083c0d800302058002c51081d88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 547795620 1250 547794370 547794391
    0x6020304030215090d060209040b01020a05280503070c05010e010314010306020a0509040212010915030308010b0703110f0624180a1404110f04050402010c1209080a0302030903070914 80
    0x92907601854802d540d40035100605d64545002d491610900a6000c400c0490260742003400312070780d03903001140942c5620f802c5006410100a2000c041c0001540b0500c1e07044070403101402c20740811030800c050624030f44030b4500000020704000014211a204901442c101800c241c8118420b810045105045070382c403030030241c0c03200e2a201041d1818014160f490360494030200b891544168516191ba040701c11102e0104503079014840600300c8007000d404058041401d80d00100302c64490003008280041c000e19000c40b02140c481560382c00c0041455080e1040c1c3e0000d014407a040100401044000038410001b800c04c80c00100416912498002d03483d82514003034001501070300c0b580d000140380c82c080c0f42e100e414615051400c6a84843d281c000303d4022465040402c13102c1c20075216540c02150144c403000e9a00340103995410200081481010410454005c0021419020400f0714451403081d00603503243d0806800b032610348442c80e4000c80002c4d081454241e491071804c6815900101503c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 547796870 1250 547795620 547795639
    0x18150515071b0803071109010e06090403080c070b04111918050c0d020c030711030318040534030f021306050f091306090b010201050108030306010f021f200301060203040302 76
    0x101400030800c82644003c034140000030300301c400c000c8400c0c04000b46100880311600b00e640c03102c4001d10400c60071203403203400040b4039002c280481c1c082c00c3c006500181c040b0400340b6140c1581c0c0e520102070710075182124018030104010219141c440005075400c035000024000c01858169100c00c00c001040700395038000e07920000314015481038022180000a5848195994104c500c1110b0362940107510544000065107140c009a103070210840340d40c400052081e401017141202000010311018007003080504025030b000402c0000006e0340007122102e0107100d40240c109910203800e555612071202c034082e1040140c1107011900b248880c055030450300d4099161b03070640c00104020302c1103400c250f905c2034041400c43c940140a400c40019591400300500c048184000160300b81e803000e00030101c0d2a00240000703007140d44288016200c80045204844c1050844000b22080300018104407004607250a4400503609248044640240c081c4090a01e9903240000007503e9019a000c002d105000c1c14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 547798120 1250 547796870 547796903
    0x11d0d03091a03090f01020a0503070f0c120f02010e0a170a0504081209040c08070c03050904020706050f04260702010f030b040f090b01050a0f0509101815051507 71
    0x888a03440541944114a03003040704101044505800481d400035aa00c00c2c030040c217001c0d00e01070003911005282d41d10341c1421910ba111041d2520568040a8010410001403800118842111503900c48a2030b46445060441100d002420740b011000c6040599002c040c0540000d0010b241c0590781c1c14920794095103c0360080011115071090313034880c0384548662240d886901d5408802403800b508106c400f080640302c4410107840c1c00034200c0e40300c00440d19281880740428018001002401801040103140c412181d403600110394040e03440201c0c0319200b508100400c0000410251108441310195828070300407180b142c028451044000d0420400354504048180245c002c2900b0500041050054035640d034034440041c02d400c44260f411038100400060281814504503058400b031807400c100c45400c20301400210000602508443c810300705002039645800c14142d803210074414004596407842c0002e1012a01c0190070441c41a08200061203c80101d98120340c980c03039220501c1d01520088 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 547799370 1250 547798120 547798127
    0x131502091c0501050118050f060405091f0203100f05150a02010207121806090501020d030e0c030102130e0703020306060d0b0d170408011a01051b0106051815011d0d03 73
    0x8030100074180c00c601d10780d6070003044010f401c6181620580d1001400c061204103501d401d6130020b640d005c402c52040c0e00490914202500203d5010300494111042154000400140340040c082140003072a0f020092011200c43d04406100401d06070896040d03090034800010070001508103100d5503da030004204c80424001e405566000c0e0300413250140e0010b1303102c1c024004a4201c800c0b41d0a514400340b01084443c018276003c01134960603030040880c0f8498400950040c8800050f0000342d01c183c940c2d5003042d640900007000910701100e4450002c5141041029400c04040d00300344c240343c0180100005901c1d8030b419260044c0c036928000c9040280301d00410f1842e00b000c1c0010b0b04030340d41794020001c4004a840240708840310325000700401c0c4541c146c0d1143da17450003507943d800110100b110b6000d0740050b454800804916000005589544a001617035080c0304a06c0d18230440003400400c5401500250560f1200c102820006202440340c918030003607102e1110f28512031a10709000d482454030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 547800620 1250 547799370 547799389
    0x21215180a0b040603030c06140708150409080408010c1209050613080712081014150a02070f0801090201170f0c0c01020d0905060f090a1a06060d021c0513150209 71
    0x4043c3c410007450741c603401c000b0810850068103841440c20540f0414814000e010b05d030f4800c0005540390095074840c464070103043c4001d09590f80e800350b1101d4a07040824810740c0100010441c0d00c00001d001c2c0c0b00004007403c44900d0349068034000b403901403010081200400c11030390000e603111910202c0344141c50641014002c58601030031040c031020140c2c15158000041c9402107014213200d140c01540c440d007000c0c070803030454070007500016030782201044520300c6405803c03008071a005031440380c0c2d12210644660200d42c2e0104109070b4607030a0f21010365803c201400350803000f6aa24010f60b20742410680b03c150b1001d004038441035800220281000400e40c103864840d6550241803103085040c0c109130703035101010b030384402007401264041303812904000703a507403940c40e8090540b00125210110445260340000d094075040403080000d6881110144020f000400901c0c900b814080d044002030b00845100400854801c000e101d00e503c0825600140141401c4640001598400031100414a1600d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 547801870 1250 547800620 547800641
    0x1060f140a030504030e0a05030307110f10022b02030307180f060e0307141003230c030403030c05090609040209030717060411060a080423060901021215180a 69
    0x2022400d0340718164076400160086029035149403009050000f04401d110407885000d515038010044000001d20714a280c10240300001e1400d902c00411201044002910503401001a0012400740045099801c50340340440380d0407402e526018180d080c042c1d900d21024154406000c2d0108120450041c2c00505c1e1010b0449000101041e076500c0302d003c0d00300c010f401c0340d0f184240168000401c0000800320116800c0d80014004100b0010804040d4000d140d01025048400021030041d80500301d15950076010315034552020b5941e10b02410018121046001c540040050400c000e00c910761355001901c004143c12100141d5554640f00080d1030084a6030000300d00040b000c0d80f070985040f02040c22031069000741e944903448c4091504000a5218201c00c28022034014008100031803c440703580c010149000503c04120b0001c820403a1410804644401e4569000104040b00500d4580750a8001010303041e0480854881000540c5800084140c00009030070030000400d40e00301c0750406428407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 547803120 1250 547801870 547801907
    0x801030212011b022b02030708030c040e04200f030d030f062309070309080d02092707091205030d0513080a021c110705061804021305190305030301060f 67
    0x1e40f03400c034020b52100724810217070725401d05010400601c8030341c40b00e241c4202aa0f907030142d4a084450354030300e00c00e030700064600c400712002070001090b40e246074170845000340d00034040c0220440c14512a8680606002e1070705004840058112425440014100529070007c2c103011400000c03d403800c000078401c03a4450b0100c080da0030b415504c004403010b800291203034203540c801401d688018056041c0d07001c1107401801a00100032208401c90151b02400c11800b00034140e031401c801f082a683c0d4201104110300301c000c42c07510188aa102d40280c00d6500500f118803450102003803603190b540c0c40b809254000040d180c0c803003001444442c0301c0d0810003811070784010320945440668034000e5403810034004940c4c1d00141520f021040c070740120155000c40b110709000b0701c00302d401c000c148030791038010403402d14201c0c20f596000b04c265174a40c00903107500c0b5403162110641038900020480100c1542149001c0807100b0581840403c00120031a41940c40ea07041503900b02d030071880105c0e243c040c401c2ca542d250 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 547804370 1250 547803120 547803161
    0xe01110604150c0504080d180506070c0806060102070e0a050901091a07020c0d200406120f0210030504030219150507030b030c1c061107050628020a080103021201 71
    0x2080407502110540101c40c2c40300300310398240c1120650f0a48101d0040c40703895403100c9a1840c0c3c9620908690a0005540c200e04100c0ca90300c2c1c002c00c01540014000b1218041040c8060003280002c110a950200d001d100404c0e5080c42d10b0100032031850082c00f1b014800e40c03503400165a600b400d4210311001540321410080c2c0e00044199410002c2060f500d081c010f000d96a959801c62414990850015401107444d541800b0b11071b40d80c04d0003031345101d2283e0304180c80340000204407014408002d9541d0081481e80c01140b914410015a50b030324a96603c02c0c18070700010f11003c07960004880e101c100035501700448480c070340e042c2043c603520f01d25424180503081c101003001035641030b000030014442c00c0c0d0890304203074050410802c00f001800c40d401d009400324041e00010030019080303030400509100e2510300d004400d0704c1e890704011084aa036541404410b4588503101071400c070f260700100d0740d08011410042140c4009040c0c1d0310602c0064858654109139095480c000c7d402201112049040d4031403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 547805620 1250 547804370 547804373
    0x1206062d1d0f121c0c0305040618091814060c030c0d09060203130201020c10051e070f081213021c050309090f01060f080417071403210a0b090402010e01110604 70
    0x1596241e4003040421859038122404c0c03214096005210003981c980c45203400c240c2400400c6450010411007650400c02e11b00000072000a544070310302c0346041042030140b2252060403e214103802c540812891640300e40308025810180000f80c3c2e41240b8403400440d41d91140054220180403190405444a44000300303000c80c401c41040749692140c0300780c09903600007504008008005651300c00c0040818001c0103054220584140000344e140b940120842c1010720f80d46401900c0c506070182203c0099001450b41e000c10702002100c1c2d17019001d80c104510704100c95000c00d02d248240b1100b003e01d1840e00c0e80360010000d0510a40f9001880a4007038011481c202045c1403180b58288525400300c0d07160000c2e581031a100e0040c01d0710854010b00c016100c48060340704e880041d4400102550080400c1003e41000f000600080c4541aa40700c020742d840401c000c01d441d030340203000e040002960302d854851040c94591040407a4404d40908004501d60590720069a501c048880042d01d140282e80c100030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 547806870 1250 547805620 547805623
    0x60206090628470f030f0a0614010f140f062101050103051303170c0403080a020f06100303120507030e190b0a0b090c07031206062d1d0f12 61
    0x2840c0040c2542c1420071800d100c0c0000240000380446000f00800c2c2040c58581c1001c4144454034034001d411144960700d066200c41c2040c0142c1c030101e601503159031840c4004181e0303405440c0586950264030902518005204100c00c04410885014001b10011144166200d40990300c1c2140300341510030380c0c9031140303081d04040a02401854046071801c0d01241090b446c3c1050714501c0b0f075240d21030700ca41c1c4103202e85142003038000502c90700c10b0b0281000007100203246d000103044004000e4000341042c00708001117034108a00109a840751100e100c50030030201c0e500803502c03804250031000000f0561508842203010b8012039144420500c51300c5010112050206802c02d50f00d4059031030400f02d40c40d10b80d000000d80d00c07102e4004c2d6000503840d01148400d2042401801ca0302d1190514150118840c0141c0341a520140e02c4480440d8078410303108034401c004a0421000d00d021600042c40e00b0304000082d041052041180684e20b1603000c82c0c0c5026202d10b074021000c004028080c25480c021440503d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 547808120 1250 547806870 547806911
    0x70f0201062616050d02041805010c0503070813020d0305160206160204060504060b0304151b0917010c200c030106151e0e061c11040807060206090628 66
    0x503400307110340c403e4007a815014800803400e50307000421400410500f60204009081501000840b42d6015040800014024410750b21502c059441d4107469113007420380070700b00010003485290980d48110006005a83c1d2420600b0000ea060070241d8881004c101c3d420300104021400a420000003c0c00007a18080f010154113818400ca40620115481c0c0050005481880c481c807240c2c3c9905001140004007104001ca548051280700080d2a08098804040380d101001e8524080b6024140c14440100c221103140740307241160001b4030107080515802001c503001150f40e15440440600c0240c0140d1007400348084001000f002400b0f456102d044000d40906030700d00310004501003d140001c042d070321840408014009841d601c004000b40700621419604c10115000e07903500e00400c1742c00c070300350501c9800c2103d4440194251228205403d16283c14040e4008506640c041c500700040060001051540300121020488107000103443c88030114081002c1c101105080c1404a4110100395040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 547809370 1250 547808120 547808189
    0x20904060902101206060e10031e06030c05010f030e1b0f090108010b0108060d0804030b13050307060e1212010506070611300906060d020f0d1b050f0108070f020106 72
    0x802c02583e40d10419200d8850a094840d0003020070603d11400c18007a601c14415080c104074500a0101070003080421629290021915130437141c40600032541d1002803ea034026482c05c0c00c0203402c0030710100319910044c05e904a2f034a6a079060400d406a116500ca2110001001c0c5ca018140d585501d105c1340a03082c00c0750071500080340c03040010007502c1d002d00300402c510b4100e41150715140c02c6850760084504014454480f042101d04810001b030030801c01006800c3c052000006c0c0c54400081d03080c24481006582e075203900e000c0c41a20705121b00383c45154116101182da1030340c1e50a00d4984076015140040004148844c04190008510402d040d001c81071481c40010a4070881305e819039003c180016100c988056005c00002912818104896000107000070440400740c59010300040e0010340c0010100c44a103181981040700340c82d10020180035090845460b80c2d403800100000f807101100034800010400b1000c0e0602509000794002000750501c50740e501070940501c0880102c0c07050118a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 547810620 1250 547809370 547809407
    0xe012007060c0f1d031e03030411090c04170109051507080a060e070e01020708120405010305130f0f0c09050f061311030a0e030d0c030b090f0f0402090406090210 71
    0x240d0900c0284140c2650b1a003403059110402c0d501c42580320003618603910f00f0390341c0d014450461080c0c1189801b480504020b1030704002180e4900d8146030880703d1609214006010303050101c02d10074010882401e450a0b06c06400140e2403c0305095002405021901000750060080c07104101d8200c054211451251038961101d42607074940100074411a102842021920f403190008103010700c0c407990300501d88400500c1107405494440c080c15040812003803034031ba80c0c1c180c00a000c003e2542c00d80145940103054585041110603240c0750200c0b580030074071004140400441c0894100300d245507203200a48001e22040009281004203d501d5800545000d441a404540e10303000b94016402500d18070707100e0301c1c40c05056440d102c00010103030030300702000000350000380046d917100c4440744201c808642c210ba6002c40d039000c819003071004501c40607110f5024464004108204c000003a40079a8000398181c3c2e10340210342d181c0c20300c1c1000700450341c0003d51200c00c00e416020b12503400600703400d480561a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 547811870 1250 547810620 547810631
    0x5040e0a23130201111606050418110a0804020109090507020703110409050d110a0b102c0c16051c0305070e01020a020d050c030a2915040e01200706 65
    0x1800500980e10441e1180c8000103200b10750740c0107500c10901c00030b45441c03040c00c8412900d0401d0030040401c005410001c005407000c01e003000030703804110b11034100d420030100800a008114140c01024800c9015800c140510345021030211391144000d03500034188403500f0481820100c00003034944515100580d0045d2081c48054510314103031060755074499201000300000d00700d40406841035941020300200f54051125190082414402c100703103d0001c8251560034581401d00040b05200000d0080b0803070120008001c00c4074056104051300a03a03100030282cac441e40510540d41403c000100000c145024a5100c4213012401c904074010900351510240081d6503458011520740b100c0f40740c51401640300104070400f40c140035444d11055409101681c119001c0b08001c203180c205120700880710021070042c0c82c1d211001c907041c113078202d121541046005003003202e1514020b0818800d41ca220b06d60354080f003100314200350b00042d03a0004250754003c440e1500c0900d054a5001946c0c02c0d10200d0426 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 547813120 1250 547811870 547811921
    0x310080322050f090a0c021603050619020301030305040605030a06050a080d120507021b120d051306020312041e0507120606080309091f05060304141009050c06070305040e0a 76
    0x410781c030102040c00303841c4140720354400307031858050301c1c04000b01000c7d03000e5415080040c64040c0c01404c085e501400c01400c0d10b0034411454400503050002c40060303548148014400640d010301158116074a0740341c03d684940b543c1e40c02c3c0c001800668041d55102c00c0c0440e00055030000031a4018007c0000c0d00c4003441e2018501c0391405a541c100c42e502c006030407102c01061900d0b040180c134240380308003400030203a1071850280c551074944440c03100000318001085400e0031a000c00c1800c4060a0700d440a503003081c20700c810040c0504009440204030540380545008401d21000041d11030303c3d04001100d003c031741e0715680c00010a1504805480040c182000070850303500000440e816003402074100030280e070356a0800100220340c0310000443c444070640014880d44d41001441c0524014002c12a89a03844503502d450046a003400c80c2455041c040051301146022405004140b070603200319660319900c0c0b9040b9142c0c41140c215100011011b410700002c2c10503a804054407042c052081c5c0401d8115 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 547814370 1250 547813120 547813129
    0x8060307080309060a090b0409020405190e04172b0605030105010e0a150b040b0a08011508040303020f0c061302010f211104030210121107020d0602031008032205 71
    0x5405696103030b61007041003441d581031010042c81c0203565443c01c0c00d40d59031184507450722075006900c170351120340d0041030900661905480c050140000500b2030301f200d03882c04961600701c0704010000b4004040241d0141c20400558040340c1125103010f00075110007c0794410001000041107410b1089840d00ca000f241e0790405200301d40c1a20688489250187d80e440c0d281d10242680245ca410507810b01d03030001502e0a010b20207013000d04241214151a000f82d20002004054140d0240d40e2a000303040d105c005940d04203804d50f4126070589400350340c3e5000840348188510980100c65402d101b44810030a01c5a0180300000c003651003640d0302d036070b44031204e9030440d44524803021381045090036640c20164030907982c0c441c058880d40d0403410303401c0a54980004410390317031004110001c1000f0002a80c02022584117901001d04890102e50900701a5004100c120040300c00042010790300201042604a641071a4401000304200312584c40c900900381e48074030045d5004800c0001d40d140d4002c5901e151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 547815620 1250 547814370 547814383
    0x30906030624020a0b010b0405130218040e012d140603060a0c030906020d020d05060307080a0303020c0726070602070605070f02012f1014070f050c1c080603 69
    0x401c1c160402e21000003a484032158018880800961207100f0000d0000307010344c4da100b4028640c101440d40c40d0f0b0b00e04814008981581c001d0801021320400030380400d0041c030828075007042019200000c600c8c0604500500501014100101c5080c5090322030300c1b42d40c5000009405600d20940038804001d01000c49481c0d600160b030318541c550020303000911a040f607584050f444039120b1901003074806464603407504a0f842210a850409e8001072421070780c038400d0007200d0300701c402036006064551501880c1501c450060f0401010550002040b02e00b403082042000007910009031084116000b0032070140240c030b410344803d003180c000c1e0100025560f001184580450305941c44180c545403c1c0c1d600e10301e0803411000103d040c007100280d1101c2100c0588200a0b80c80400201060b0080c241e0580e51b1400c604035400c82011802e03d17100105c0500395407591900f004050038107030b9803041d56045c1aa2540114021000306104800444118042c019000c4120459580f580c0c802516031005050f203039003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 547816870 1250 547815620 547815629
    0x9021c02011b0f0305160b10031209060206151306060c02030709050c0417030c0a06150b031e09070803032412120306060f0c0c0a060804050613060b04180309060306 72
    0x501220240d00813038040c200914540f140d950107442d14a005a4403025110002d4a8200d0040f000d01d10034010000d50b0102e02d00c031011141041c008052034440029078416005010086010b008000504607880d4808401c0f15a0130074003007401023a4507001c0003050502c40003000c1c6d220744070384000002c1109003485198010b4200b148514685410103407014a1401c1d515102c04492004025204c03c050080c01081880f9110b00f0011809150b482070390902c241068024a100640400501802c244800b8260080035800e4004040da0f03681d80740d0103070400c0d0301c551022085010020400040802003103e0045064070080510034500c421802d1142d15680c0d0049210039030300503030f1072442c040e0040c4080d5601c05402404146801c08010100c40980c0082030151020b81c44444050440d2402e181140701901ca02d03e8448098034154650039901c1001800d2101800782e06102c4134140001038010381300c1070720302500a10030000d80c0d03e0312401104201d541030340090141d00d404a01c00c4e21a000b0171341140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 547818120 1250 547816870 547816883
    0x50c0a260a0801050d020d0218040204060906081b0a1e1a07050c0d020411040b07061a0a0308130b1207031118190905160210150905060409021c02011b 66
    0xf40c3c00c000c1400714040c4204070603603200301c48030795000041e0740712641c02060303501440382d0244505142c4140000e0755030325000400920305108040c032501d840014010200214448503444107030400700811074854507900b10b408003103250400b4051000005a64000319000d5800e044040105022904000c0c040c154008240f604200b40c019018500080011a01400140000740400c0c1010716040c80d9030050344410345661000c544241032004600c40c900308100d8801a195420041d01c00281c0c1c00075017404003c006c1340300802c45103c82050784a0f254080c021516400396918205902c864a4850488a00700024103186050024036003010944113289150f0171012180d40141d0104100d6080186c1042944100c040b400103a541c55070003024064009400002d410309103414000b410503207030040480c11141044101c00304c0100d040060b44c11182000300009840d1500e00003c2c1c003415903204081e44c40a0400d5280103200251441c00c44043d200340c071651440000c0d8080414480d40401c4041c000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 547819370 1250 547818120 547818137
    0x1150201110d150905090c03010b030d080610021234081606140a0903020d0f121a190510170103020105070f080304051c0302031b0a050c0a260a 63
    0x2507a8294002c02103419885252030180c44d02c40741a2070840c0da0840300c10020394400740e8807078558102071080d400036040540250680011000c0c0c00f9240707136030280c00d0500450024940d1303801c0f0307442072000900794a00b070910681c1c0e84444101000040c01c86515044550030001206c50313039030f400d00d4071130b02003681c2c0144c4541c02c201202600003461010340c030007a601c44e81c8409422030501c2d007015485200741486040042c8603e80da09000303103401e41500c2c0a5040c8884600c00c01c0001b904018040304505200e440450f1007501100142011403803000e1b91134109482e40084500380744c0d41ca04007400c1c0c503c161148a100d00785c0c154221030f0100d8800f20414070900710401400035500c00d00040c10710030b010b0380703400040c40701d10342e2031a00e568800c4a040d40c4c143c03c0407900c0c802400782050000800303101c0c1e107020750450802d4510000951124030b4900680c1e070000580d03c801074005c106890303000703074140c041d03400d035a07c2401e2480c030010160a42d131400c061100c50011306607130640d065580c0c100469599504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 547820620 1250 547819370 547819387
    0x3090d05090f091008060105010c030c112b0b100f03020409030c021302030103020406090504021c030909020406200a0b0f0417041205060702030c12031812030115020111 74
    0xd80d40c1c000d44445801c550341c402c81204079110003260501400e0302100c80b840841c40c040c15941041e0040c0c125038100b1209007005008a03900c07200401010b60400c00404242d180300380010580d00c020005246e10400b10800030306080e1001d41e0815003140101d640ca0038070703581c0c62442e901e5140d10380a0900c41003201d42051015040c13603030000101c64480e0030254200a4103400040d800950302e00c00040306600000140214109405200010040c107941401141841c0e80000c14a02071001ca002400c04031103128000d242c4900c2c85080201380d0307010119603654690000070071404518040006015820080e0340c0c84880c0010007000c06074100203144660303250950814008480070b00b0070703910000c00d2040c0c00e51038005503004000400c4074817080c010f038030320624105082146c0106550250341081c4070380c45411101241088440340a0011b8960741c0e51906000c4d01c1c5001c030300211203024441d0a800c0003401103448002c6041e84c0c40c10086040c4448842d00c124243e44115410341c0c52100140103112 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 547821870 1250 547820620 547820627
    0x306080d140c0303090d030e01090206030112051f09020103060803070503120c130e0105010f0801030c150507050f0606090c070c0909030c0f06021b01020304080a050a1205151503090d 80
    0x12030341d00340404880c03900440080061075600243d0300311150384c201e00621800c042d014454001080350100080c8036880b004c0c0c00055040c001485101500241c8015036001c0240c00c0c414840402c84c0c0c11940300410400400d041c00070700ca003000c2280403900d072400c0480e440320004184e8803410b40c007074000c40c40e0000412481035600030240a032010850701b40444a1400209041e02e806005824202484c035807400000528403000c010281e01030020600c01400454442c1c03060300f00b5078002030110441150345410850b018420b00b0000307803060107000001900d90201082681c00791100300e0b20042c06403101c1250200354070401e03c000304107500002007003164452a401c41d521040c064184035201200c20385034444d074102c004800700c0b911b50340000d07104208030030030710900c0201c49a84000c50442c9030581da00050392043c4c107110414880c010441b1550b841c07003002100c46410b02c00b001444641402c2d031100e00e0103c0310410303045c4924004000601c10f6070101050780e04c2180440020300c5060340950059 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 547823120 1250 547821870 547821887
    0x6040618080301060f2706032f030405071a0d0b1302030a05060405010b1309110f130303030b0105090d2303130906060c02030d140d0c0e0901060306080d 67
    0x468501000c0300103001141000000e903000f400c580e111000030201c812001807094500603400103030b141c007510030081c1010040c100e4400355552410001244003915a80e42c0110400c400c090241404d04c0030310201c51542c21001d1070155200c2d5045991f0756484915841e04082d14202c00d05280d1014004140f03400181d4200780314000d005007851049d95004c51545060380e00441304ca580703494582d01809070030f003014400d0340e0041402d0200c2c3c908000036904030021684031807062862164907008183e400c1703e40c00e822900c18076500740c07580d40e0354800c200b025101c11040e84415008a8600986907010b94010130480d028000000e0075444060910741d55488062100300c0e0180b07407965219a100c5403c40104000d16a03007407910348100d401840c04186105a0b031564010904220b0406043d10040e10b00007110b442480481c00c0c401101d0203c1490350309113000d1814125601800c020b9601d40d429000107102000ca041514540007503078a545040e03003610460b10842c0c03000ea100304440c4c40711038806c0488 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 547824370 1250 547823120 547823141
    0x1a04020c1e030715090f14010902012003040603020d0b0a060f02121626130f0f080d0503090c0d0b01030605160906110f01051e07140f09040b090a0f0c050705060406 72
    0x440c00c891030a85640b0900087c90141c402641e6413134200105640e000300c1c440250041c4980b1031f0720f10010b004d81307681c1c50303001c0c901c1840141500031030030b07001503a001d4002c0c810f825005000000c0b030342c0e0341e060018032041028401c88054081e0b1821004580c0c1d1035012165009604900000303250125078500111424120340c491808015040d40200c11050703034010010001c0d88444030000c07034282003a0304125085039002c0c03c510701c0045001c20240c040403414030340380c9141d41403042c2c59607a1070440b41c0c20041c1480c5280d6000b5243d003094420800700c508294141c034000c210030086c0d0398510b075000904040e2428004041100c07e8402c1285c1c1d44035100e65048002c1050580300c0a1003c4030388582036810945001d400340d172442d011604400074040030190701140da49002c040c03050940c48000b103540f0038041741058460300001c02d41c1098865400040ca00440502100e110b460500c2c4410018040d042d214403c290500d2100550688100281c64196802c200039050540300e176650f00c001412012030b03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 547825620 1250 547824370 547824383
    0x170610051c0f0f060504050f04111519090602010c08010b0a0c020a03060207060b01020a0c0510030608151006090617060f090405010b0901090614041a04020c1e03071509 74
    0x120541950342030040042c0a0035003007001c1424488403410780183e03020f541141c1e0041e0f190000300204841d0075003540e07800c41d40207182420f41f82090404200308030f103001460450800002000440b0340d03400b0960703000714665030b03407401255a200c40d0124265070280c070f80701002442c0000140020114040100440d5a00e818400ca1202059010a12024150b407003038039000d41c0400c1150600074140101030700c0c1c400c00d101505914200e41d4612000209500446008102002e01018002d0080d405903010344100d50031501d03c0d19070690815800302088410301c02e9401141d500080140c0074044070350550300a5122521030210b5803070640c4034800c001b803a06a00070050f1010301010f0312003800490046001c1d40021400708640c200b84845414180c2c069040d1500d00441041000880e4140e0f922403d401c03036000c0340008407009686c2d940e44064504981c007920010b00d201c020b030340c00900c840420f20124401c031442901c2d031000030344034010750314040c0090000511000c10501a0341c1715000700c41c0b0424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 547826870 1250 547825620 547825657
    0x70f030c0c0f0b07121e0c0905030a150b13051501030608070e09030d02070b0117060c0d050711011e050907060c03051c0f0207060513080a0e0f0907020102030717061005 74
    0x401d00c2c0c00f0f89040c003030340c8694a160000c540c400d604250054854010080c08d00d0303203456152101183d910004541c01508150201034000811160b07600403402800000f04202241200c1900d0000185801d17200e02400c000d0400c0309200550081c001c503000c80d90104040d041700c0b0b252181056841000400f0031600340020001c20810600c02d2010740521409160b00d40c2140d81000724010030808142c100d060268010010051803036240780482e41c03040c0d000380010030141ca401e40150750980352000300000715404c6c2502813903528403c0080707440032100030505204ca91070701040b0546806c00d90090f080001c101d1020900424024001855002484081c0010305a03410300c2d50740407140f0a0221048590300024000c0070f110080c05441d82014120048904100d081c0e51500c2091080d05030300c07010f02055049001e0242d668400032010300c400a814049036103440b06000b8001d40c400c0750002c000c11003403008252980e41b0241418441d160241410b005078401c04420340300c58021011103040070f0604d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 547828120 1250 547826870 547826897
    0x50103230c010e150708220605070831060806010e0906150903100c02070314030c0606130f230907030809210a1104051e01180b0603070f030c0c0f0b07 66
    0x2c003106031f405026465503000c0e80f20001740001c0158441d000700070003070001d600822000411510f5410150303510b0b0ba8007601482303210303030468800c21a5220f0420100c800151454200d0299480f42d98240d0311254a60050390400156a0f0103a40d40c0e80c200407c500b2645503240080c1c01088070f200014111000c080e00d10b545c003c1560000900031005030000c1008004000d14100e641c6101410a80030714201154143c0d00c60b80c542c4010845489040030043c80705407401d956002088240c0180400d000d50490000010015840408a08440f542d988001203400001183c4002501e5205500c91300c0c0c104500100641d0f804170600c00300c80d00c0a120401c1c103174004d0421258013031a11035426103411800c0e01003000100d5100810030842c00711915003088040c100000c21318151000c68100801c0a910003403000d0050a00a020540024002060020161b0800070600300e80205503401e00000c1d00094040f0780440c8900002891311090001800002cac20b640390036030f4030044d50b03e407804802c0f125 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 547829370 1250 547828120 547828133
    0x11031611030d0e0109060302030408030f181204180605060a030209011704051f0c0507030c080c0105040f0b07030218130e07060908011104030c05130f050103230c010e1507 75
    0x2002d0588003040d1500940e400658001402000810050030214110310706034990001c00d1000070300820a00001d50000b42e001c16107a5580240040042c0c00c86049a441b0001002c09034024043e07007403146000c50000303a8408a0707000b0035003520006400c0038101100d4078030940294219091040c1403040c00070641a118800656071441580a4070080ca01c00d00c0f001701c901031800d000511075840c142080c0b03070380860070780010817200e000d949403406690440c51418880c7c2c05010785502000c0a508020500052128141c110b10350507004a08102d02c1da110504150100d04c9000d40303d140c0c1d014207502d204c3d05482c010302c8a1002c0c001c8540003003440d081c00441c10781082400d400c45000f05008410600c404c0c0424401c1104154001045a29042c110f072a00444200c203445091710407500c0400d0030035000e0903034026440f1012081814422035031a032801e01200b2100c40d551201c00303802c012502d1407690001603404207403401a100c103102c98500d1410b002038500d0b40903039607214803c00c00001001510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 547830620 1250 547829370 547829383
    0x15142d0f27180f0f01060207050f01020a0506130c0803270f040c020318010207180905120301151b020127080f0102070308010e040c09020a0905040e0a121103161103 72
    0x40c4020507000e0324105030f20307101e20100900300000d80603189005110749500003580360203851040320b042c06d00361140c600403890081c000710000c00d02d018960a020007150380300d42080842e8802c0140c08030294580d480c055072806036840c402e40d41c03404008041c0c150034404804140c250009000c0c0e01441c410300c0c002c01d05840310002c1140059000103140c1c41c4070509440c0300100c1d65000d102034000b107071070b250992048400c24602c07404415610342c10201000340030440c160512140c440340e907441e5a0350f203442c3d6055800902e94000421031003a1080024604034003110395007a130503112a441810308107881e03555882d007000086c000078240342006c50345010030082c640800409600241c1e031902a03140c0200581d8043c0e010494420350b2405000c0021440240c48060f501820401601c8a041c52001c40f00b80388180d104580091a04401d01e6007c90045003e18416000e00e6601c6150140440f04450f101550514030710340f07420030b0102c4890200309101e04c400c40d0307014103a41c0c0050f05c04c000001e0308010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 547831870 1250 547830620 547830649
    0x6010e10080a0501050d0b0a020906070c0314070f2303031c020414010207150810030b0a2406021e0a0c080d0215040b0115142d0f27 58
    0x406681c00c104495030b1074040d903405004161201002c2154542d03650352559800f810800145801184000d001d1301d401040e10718440d0010614070155a03642031119540e0102504070411b40500c03000070a10700c03d280000006c079006aa106525410b030b1311200859502030342440355141c0001c116030762170030001842c04100000e02c160016580d034908020b00000e48a480c0015040d03402070300341040743c5081200b02c184e01c1050760811060039542c02110300325051940e08000e0407c4c90740d0b018001c14104541c00444105140c0c0182c4624248640211503072108510030b100040c0d01c0030814141c28030081c00c2c8840e100c207500e0107c07151b4017450f56a850391098150080342855101c1c2ea000e000301c40c1c0c1080694400050010490014145500d4040458105000300c134048010a00340200b070a204029156924614003911a1200318061301003003520108602c80802c070b4840240e40082140b107204407050190001c0c15249441c0b0b01640e00b94500c0e64541d0391070400c08491125002a40765800c100c107444 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 547833120 1250 547831870 547831877
    0x70b0f0414030c0102030a121e0903030c030b060405060705120d0c081f0308092206050a0e2505070807030c021e0d0206030c0f120402330306010e10 65
    0xc504000700500746100304400c80348640d0000f981014640d80100072121007664510b40b00a16001d8403811002400d0f0144d0b10383c1180c0300164032024220300c0d55005a400900c0b80e43d0038400760a0100c821025100600704155100c0002c2004020030301d01840144049889003080e1110358150030701101090300b00e810f80f00075403501c420180c848503a02241c4030f81d1003110204017030050b09191745095404404c81c040200440000101c402150b50303010004140440c00c012094400c02d04062000b003d1311716441400d011b903030500300101d42c196040c0c20140c802c020803001841e8440320902c04030080c8140c2042441400070410200d000b1806000c020081d440c0261545040c010361841400010180440c2285030f410700c20071082c403a940e0b5003c0d00c251064044a08a0310b0391a94100b21860348a1803e00c1004510002800354581b03101c000d203284118000c0720010145105100c4c51080701e18450455030900388400309540b0342060203401781d50041d5041c9000c07480c18202601040039500c041d40c401021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 547834370 1250 547833120 547833127
    0xe070c051603050d2a060b061b010e0307030e0d0201110607030e0c04020a1e12090f06241211120c04270b06060f0f030103170a0912020102070b0f 64
    0x40c004200300032180c508981c13400400440c210b000580104011a04002c00e144190082c41c5c240903542e0803210202000426560b500c1080480b400d0f8184017601c2c21128550030240910151400401035400d41d5800d51190480041c81c10100019045540c1e0f00300d0500c120701d90300d045080c00c1040844d21a800c161000140070401c078814615000c104146a445a4010080c4405050b40310740a030b0010a0750a00c000e2070b41020502c25a10079480c100c0c0002c01c0c40c5071601880c180005000f0501029002d800100458000d005010080314541e000044010014880402c82807560150b000e804500030115000d04001c11000901c101c10700e644003218580c400103c10240745464070689840c243c540c800c40c0303c9820f0004214001444444020b45809a0600021025201d0400f180e020604182040e599000a200000030940007800150341d12406220040aa01d0020301240c148d505a622056900307032602080a0082c034504400b02c0c110700030311000160303c084a402422a43c90500e20550700c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 547835620 1250 547834370 547834373
    0x7030311160b15030a030c020919051003020f0301050402060714010f1409060f010f06030b010c0c090516110304230a0f17151501140a02010911090708010e070c051603 73
    0x8200c218643d0b58400d0b005404403000107a00000c50000117681030781e411001d40e4030710390403040700307014260303503081039401d141c100100e2114072900c2c001924821a440f0090090b10001d05d400c07520220b9001350018400c00950300411200030011b0844500c00700045503940507500c040c410781c1d5403d25040d01c0800301c6001e10000b03c07414070039581c0c05400500482943e41c542010301e4050300440c410300c2c0505035074201c01d0801d0703445030350200411504010725510f2251390304902001060111001965003c0445041a51a116445c0fa41c000c540c07800065081500300f0ba105450060050b08000405001c2d462452182d103500d69a0781c020103084c01ca0025551626244d003040780461420522a9040912454462032001d214103401c101c03041e009245091860740142e40207815140c0f04101d159011501810042d0305402001c1160310422100002044040c18000081001d4a005021802550041c800402c402c608079910548034603080ba40c6003040e4075400d081000034003480c01c40b00101c841c10b20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 547836870 1250 547835620 547835641
    0x41a120601051204022107080d140c0c01030f060314011505040207051e120c0c0109051c060f180317070c21090308030a020a0207080c0607030311160b 66
    0x940c0640c081c2400e610740740c03030884001c43c0c40800a100900c04c8400315054480c00c403039130100c21030744240c4500300c0b0296505c0d044000c1d554201034032040001005440641c0d0241740d11403d840143c850f0348004c08000d010480154042e00c115140342c1c10880d52558000040390010b20a043c20910001c00040c49100840c000084601c0c80d411050289004011080000d08005403a6440040c4c441c1d40402c513444040e03115091190700e00e03505040020201d039908075a040400c0c001d20221003602c03601081c82e5070780c092100c20402202c1401c040c1075200001800b250090f00141a000f0a142c0c00295540302c405001280045c031500030750004030b07004001008404642c1e000d03900802c1c24140449102c0d5103950b01050444002c480c0b01800114a00c09104e060240032280c01445c2d00c03503141078803864688000c1e8000d4202e43d10050042c0b1034104001908030021411510440001d002d4a2811906440603400307414465559482c10104101800000040318141071425215082e441c9050620b8038020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 547838120 1250 547836870 547836907
    0x30314010906051503100503010504080c21070b06030c150a02010501090e0705131e0b181012031e03090311070b310f0807061d040908041a 61
    0x78440079140400a00181d41c031041129507110a801c0743c03540d40d40da100304482981502da8803c0c1c2d01582030505110070070030710102510111030400300b25144c4807d410070703c0010f80400840d9240b0072004000390004185241090341d407094024003192105068100420366002115991401902010070761541803070303083c01542d0041502050601c41420421300d120b07140c034807510419204620880c02c00002546c20303001030300108407007a000c2482c40d414054110181100b50090b5118a04a040380e640107403200e10160f00414000158023000303810005c1401d01e003500300c1000d40920550f0a500781c0c4104030314000d1001040144d070040340c28645441c01910b4404409800c0311039400002d4180003100380001a5075405101102c2201e482a0298140c0b484021319808c00306805d90100006c220003c401d400300044801c01c1c421609801d074ac80f0404c64000f13910481103045010055a000e00501d02a00000600b60152128a00d050380d641c002c03039101ca00100e10b00310002c6012130f080580a401070380301c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 547839370 1250 547838120 547838129
    0xd030608011a21071e05010e03030307020a0308070522090e03160303020304020103020f0711030d0f080f100e09010f0f06030b04060504080d02040602060402030607090f09022503031401 81
    0x180180c46580000070b101c450900515040f4030312444036480000314100004001003085c0d0300c400e101208600801a00481940034050100e40c07e55825000307400c002080300c1c4141403e42c050200400c850342d040307940840180c018020000240801c0588900840400182c4602000c41c03102035481d0096231015076400129424140e001406000207404a03500c01c5590746915181c0182d0f44c1c0d44a1005a00a0143c0104103084800110b0140c007007040341d0012854005c0100c0454003503500764031040704c80e21700183c07040c0000b4285401050b02458030b82207081d009a444021044180e0320b5402c0701c1c01c0b60b141210203861507234540006081078040e503c14102c030542e60200c148082e904540f2402440b010113040103044503524000079041c407a03031a0650b65101c00c114801d5540744ea81c0e00e0001c0d81c404042d40c06a00c640280008503c2c0d03240161445000c60b0721100380f041141d4038100d01d84e8029001210000312802d044100c0f0042d4005660344008864441e8400003032820011032130b00c0001c00305801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 547840620 1250 547839370 547839401
    0x3050d0e0306150307030f1b0f12140f061015081006081015020a0605090304050f010807020c030106120b092a06041e0806090d0509010f110d03060801 66
    0x1048941c0d100414259480100d214070905043c070250042031900ba81640040d00300e10b03d48100108000c20160f2000b0741e456006211844181c4445031601248458410b401104170051040c0c000124090240250005910140d075a8202480c2e80780e4100780b0103e940d1883c1c208100d001740082c4030000c1410246140c24a01a0b456107081156440d2401550044a061007422000a07006c2c031010895a0054036404031b40070301a41c190000070b0354801001d44116542030034a03002510307400b00002500d0455034014800d80106140700011355050101520020450048803030380c02c26070f202401040010020450704400700307499810306811204000e002442d103a00320b13101060300f50103003031005000b41c3c000000240d105100500050100e11a942c8035101c2c5114841e071154101d118000c000c0100c1d0502015914559903040c2c0c1a500c4852003c0c49101160080c07112461030f51081d503182ca0159198104204070b112001c0314640303800c0d0900406c100003034840074240800c000c207020303240c5c0d107021412 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 547841726 1106 547840620 547840637
    0xb13050a05030a0908190f02060c0327010305040b01031104021309020309120a05040b180306040b04061508070510030212090c0102010c170a0f0e01020a050403050d 72
    0x102103404601e07110400620400041240d003510f44010104652180291fa24180c000d041c00f84180d030071003c00d102030480d00c00c041008061b03d207144035424401c207000d00c001c040c040c924509814109410002480001808c0b103610709e0540e503000301a8056a090718011900a026201e06403400700301d40980011021056401503020310b42e40400d4070800e506095564103e07201e45410700700002c0b01000101300c03802c1c03c48040c240c00010340b222912610a2500000d10703145c0140e40648001d10b50070280b00401041e48103429001032800ca10f507104e84c0c40c050106450b072080340b141074064000d0291030040c0601c00d504a6415860707252070080581440c0f11103070354030340000d00d056002d90f10b00044c00300e03030784d00404e04481d0328040102c5180d40d507940c41280030041e010708400d05010545502401c03001002c00c0c009004914465a51280c0342c601e0740c2003440c50940c40c190100140100d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 547661870 547841726 := by
  have h0 := BRFrame.cov_init 547661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 547661870 ≤ n) (h2 : n < 547841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
