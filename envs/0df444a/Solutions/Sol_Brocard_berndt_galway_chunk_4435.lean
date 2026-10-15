-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4435
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:06.569219+00:00
-- url     : https://prove2.me/submissions/86913631-692c-499a-bfea-7c13ea1197c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 797482014 ≤ n < 797661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 797483264 1250 797482014 797482031
    0xb070c020a090e06040303050730060801090602071115030606071a09210a17070e060a080114060315010f05220305100912030504080d0c020c09010509090a0312 70
    0x103900f6200600215000760348010100414164148a03e40d0040300914110842d044005c1c400350b1550103031040c1042010300b04000307112200b8143d0010009002c0036000384800e810302d04040c0c0007908242002d0341c0d00d000404c107509151070503080c40701e2030806c40400541551181010300c4002d800448088800703008240425401c12541010355221b80302c0c081c000d01882071800394580c00103820510741d0b50821020703c000c1000b03e8005081140d4604072003402021580e903058102e6507801d24001807604240006100c0c036441d030340f004040703040c0d40c0041c0214026118490600c00c0e180710840c1c140401d40040b0f481c507042d540c45a00600c040c0051391800605011039500140c0d8107601103405451140500401001040400d104201e2440c1014108014020481c0c0f01d0045001e890f1103414100340d56403001034100301000c01a642c2e01c104036001085425505000a0b40c0d40400d04000c500c00c1c00030388000141d91914a159a119020034000f030240b49076950f900341c521034010891045030b10b4446024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 797484514 1250 797483264 797483279
    0x19062019080d0f0605150717030705030a050c0a0c03050702030703061d070801020c210c100b121227122d0c0f030109051c09050a030b070c020a 63
    0x190280c507001c1d404080d81d45895075000d50071a00070800c19a0201c1c2011010482c5a6801c01000380161a54004980ea0f04462500a00235a02e12401407007842010040c840310715409405940700e00c00300d1a0421160300c80304c000d0481d5004000c05072002800507085240020300c2640030304030040c8082c0840300c442d6226580c117015100790082100d40402c0c41510060f18801c10400c00008201c20381c000c520b80550344101d00c0d01d804a0464210840d204058120317841e07000641151121a1a002500c003081e48aa4450003e4056004924400d004a00c8a10b41c41c181c08240b0751209003040407202d02c0c2500785200440003800205901d4400400e410400c0d40780c0d00d0329035070721034110b0521020f010484648560794410110f029480c201e11950f0348280c2550740d6000074080b20301c2c0c6044844a1a0710101070009000d040c080030010100d0094080e4507402c0e04c050043e41000001584500540b503440c1c0c02807040c041c1c050310002d01441c0c001c0c004070700f40e64050220b0000590000d00554401d5498005c1d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 797485764 1250 797484514 797484553
    0x602120103060b04062102062a4902030405030a0c1e0807090b060d0c0c030f02030a0210091713090b330412030806190620 54
    0x1c02d450450303d60990060500c1c0912451001c0c1440500107240c50199400b048065040c541c002409800700049480000380780c0c0b0f1007855080030115095481584038041c854980022041c24000207125070b000c4101d1541040d10080034230b100002d1a202e0b410303a440d540c5011041008000c0560008000200707882d01d0504c050508140121105441d841c40d00800a15041a141da88414102c4089061001c0e02001c100361003203070340740700e00811013014190001d4068468089204200d62070801c030030040b2a00308101a07421400b0303494032140c2c0880f008083e030721303841014402e000581054006600a100381d501000310b19000704485c50040c094081a01500d5200d940c8031600e1740401141007040300d0103030180f446040030030f451420828501c2c0c12040c1010003101228105480120364a4103c4000401a10010300b61540b1200b0400100e01300035110313620a1750464003500b02003480340ac000d04a16034980480e2099501c220302881314030741c01318000100070310700d01d820b01400101080281d840d02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 797487014 1250 797485764 797485769
    0x5041b0803040e0105040606050a050d06090e0109050114070912050a02060703080a05090a0b16031b030e0124060503090304180606110606061b030403020901140108010e010311060706021201 83
    0x7507a5480c1049004421200141c0c03082e8400c908010050240c1503124081d503402c41114185551030f44140e04485e0040c020f0340c1c100820b228500480c03190000c005403c0007046030b011348000c001c504190300b00f800081130102d1b81c00004c0703400c10400308901440240403030410ba000390151000d10140e540020340304e07400300e03909400288c06141440946a0540700e417a800c41e804400500c13202c0b10f265100301105034020031040c1c88811781321041a03414025003086d402079100b10030800070865001d03000380041084007100f040c0c03980707084c241d86414103503280348280c201f4080a00190040c0f07402d03000c50301e5600080440500740030a01c000542064140302c010b002c4882020701140c091709149000f404c2c502900791003881544250103201445e15071104417040c2c051a48402580210114031f0103265205950009402111072000040d1480045445800c076a100366a5481940d80e6000000c3c2920700030700000e0714280c04840c0a11491400c40024441188103c2d005414003c034280c80c19080603099 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 797488264 1250 797487014 797487029
    0xa06020306010f080601021b030a0507090e0c0d08090f1201020c060601320d0e0a0501020d110408071401090306140103020a06022b030207050d0e0306060904020f0405041b 75
    0x110501c4141d40e08452852407142c0c040c078001015140c02d00c0001d688201d00c2c00c149004030382032081c0003441d8900380403100c0003a410004941c4000c1e41c0d02c0d1550010301d014007400d01d0030b00556903507001915100d21801d03122600148050b0900c0750700c0d8200442d02c0d1400c04143e0703006003089000c40d40a4000c0c000f41c1503401901e00a024280b03403520000d012414517007403501190310445074207126480c008023140c007150004c4101a0315a0329141c0510020120032400407070a01c2590312003410080c0540003444140500c1d6028450030360100f01041d900d000d10302420768660040301c0280900b0750b443c0072181140710305160403482540c2c0c98941008695403c0880640022079800603c02e40c01c0c101100d00050050388002e100703000c181d40c1c40d41500c5840510030081c0000042c1c080c01020300c280c040d151510303084070940d11444e8000c14040d041c141c0640c410f5029008080c00521189089001948203a40140c03072481a45030303040410004001c02041140d405542890903140d41552050000151218 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 797489514 1250 797488264 797488267
    0x50601091e030501050a0507021902010e0a08011b0c020a06050d140408030711061b070f081204110d110906120d271406070c120804050415050906120f0a0602 69
    0x42d42405130070b5400013446401624100005e0166195000400c01404c80d04c50151218890081c401200c1c0b0318010742d05142c4c0180700807004560071006512409011900b038040070b02c0e211103c50186c0e4102c64401002c3d5004980c0441007080c2c80c0210000c08e44828140e000160051903000340d0102ca52080e03900352007509000c8100702d00300c3c1c0c02424002701c0319219001000e05150204007030101d680c48805051042002040c80810440e030050301c09185544081c4641c0c03219003d03805480c0d10070085505903402c0d0a1a00e802c581070a01d04003182e04039800000c030070608449030040c03100344180a402d6a800161041e060301c05280e09200c040c04880c0240d4840d0015418100150041904c0642d480b801a1050004008020807a0742c9840c0c1d914090b2611a10760300b4900b03106d98241026840400101c3c1d070200c0780000c01000c4401001610401c03501080a911202050021030b80720b40201504098180c02040e05841c1040751543d04080c0d04080b0707144c8820070100b950404082d079200b00c525940 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 797490764 1250 797489514 797489519
    0x903090319030f090b090409230606010f0f02030d020a0e090a062d03030804020303071a0726070e0a051302070614160f140a080901060503010c0909050601091e 70
    0x1440001d8502981c041d20740709168070b0a22021714511310828886901c22030f5105c2c00581042949654210700f0140c1c5000d40388010302200065403110811180180001c4004003c944801d00694102c01980c140368001d40c10010f01049010083d40602e0149e000d002c0c84030381100035583c92090a0f0700c12001c807440481d0b66032410510300b031030200740c0008280208050600c5080b5001012190080ba40c0628140308981c45900109041d03114400d4041c2003482c06c800582c43d00764080f0800d6001d5011070b5a2014900030200c44043c2d0b0f0a070100f2010310450803000410070040c0f2401034240320080080001164554445c0007440b800d02d40b04504581e2600032803ca030500485100342c0710700808810110f200d514010904401100703444100c0c2081c4000c581d803071920f1a1084105158000422030b81a54801c5c1d580c1029080c0031048078544415800c1c031002003160b00703041c020300d10303030740c5054030786000d401d00f000142d1018010040c11281004075455001940c1e00030b00001e40c465500d00003907c3e90060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 797492014 1250 797490764 797490767
    0x4180812270d110318060a140d020319090201020a020d020406091a030d030b060a1b140f06010807050f27070c0302010c020705010c060216060f1a0a1d090309031903 72
    0x600c0c2d90702040d900e82040c40361301c0c081c054070a85e28086990848046980d000700c8501074461019040c40d0b50040440450040e400c0d44450b0700450042c1c190600d02d009c0c1090881700c2c023042d0b602e0311070024010782280030144010f0810002c00150f051000707201051060b140d028642c1141c501484400d8450f51620304802d00e42014001b0541c0920245000d000340035416010030440c0c800c1000e108200842400e4100d801060309a07900303a41988188443d0740b220041001c43d40e0b4800344440140c090046a000240e441c01c005413010884030702030318a45d6400170550811640d184141101d41c3d40078174020081c50301d2140040c642d031252046844080816400741002400c40d6040601901550301040d410b1082c0d0ba04800380c00d0300e81d503202e24096950100703c6541c0310a044500001000c542c103015419034400480c1e0003c000c1046002c0714803140350410020044603107550f01c1069052190050114001e910203600550f0000e4004212850581480007081c602030f202c2d011620035040c608800343c10036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 797493264 1250 797492014 797492027
    0x51303030e1513141219050d090606031401052401030e0d090812041a0703030e0a0c090b09040f0f020d0503070302010f11070510020309100f0b04180812270d 69
    0x244c8618001e140301a0440340510f41032103482c44c096404a014a04508403c2c4203204440600008030824000301d50549440c50142c00d00d030200b1148500004c10f20010000c051040c1ca01c140c1c0b45000741d1000c40040640300108003100e0204504241d1a201c2020380441c0420040e0607020081e60f40802551611241504082c00c41e03901a8201600300010848100c04c4416008103001d11203143d03558a4603480c0550003024180c4811126003e125445414052107100c4a411100580d605000110144017081001c1c4801c032801000c00384a04210381c041034000c2e043c03038001032014156100d04400c50f2201ca06d184c10a41048005030f4540c20000064801d170700480702c010b00c07148956410411207598040e11261b11601514440e0340c0880081c032145c174104061600e001050808021075480350031041c000e0824050070500a60500b1103000004001310f40768403903035400c0b00c21b0505001c85241c2c40c60908002421f4a84c014101513446e0282c001c80c5503802411603070503802016a8840500d018100d0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 797494514 1250 797493264 797493293
    0xe01050112021f1e031d0703060b010e0312130f08011b0905060a180f060203040305060609040c1a0706050901050402090105120706030203310b0604051303030e1513 72
    0x280120307005803a40c0d00010b200842c1407840003004203428110f04d0480043c41c11074031300f4114840407203d0762070340203020502c0010350340211800c5c018100104010b442c410070007800c50b905a800060058001961f0030007400d031407400c1800c00000b8990f2080300d032068054503000314202d80d65030710495509102c0e502000103007598504000c8211460100040e07114000d03084050f00b445900e2004014003440100e03244d0140c0f82210140585c3c548950000759241c01c030340001c4500b0712902c80420303014509661194895584901000030642c104040c032070640b00c051070b1084a081050180350002107880c05554030454206d00002481d16081c0100006010182d00550207644d1900300203011180120b080340c2500c2c42400d0244e966100e400c941c0340c203400d01060aa075544401c0050b907030f141c60b000012a1000b8098004c41810740c813400e040000b110070170713a61601c544d030340c4d84a1070000a029030001d918140480d0f00f6981380d4200070030324400d0700c3ca0440d003800c03400744c0c0503911604000c030800340700c0071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 797495764 1250 797494514 797494549
    0x70203030f090d09230411220803041811030f091e031b1606050c15133908071a2d0c0313080a020109180e0105011202 52
    0x4030f604200342c0150200764030b401003a84100c401c2c9045c0f110006143e2085141d400c0217842041a50100c004109540d04403907040b81031885d2407850000360b41013605401d8103656101c806980350a1500020340c03250a100640520142c0d01c642c0c1d074005e0654018091440364905400d00e04041c0b03411101c150030250003000600c2c14041c511b400541c402000000d9030400008070040350050f00704181540c0c070300140140320300c0c43d018031840c2c086860365011002e006c0c1410100115081019081903480c40c0110803a03200402d07500c203514900100d585442080c28181c020075000340f0406400020b030003031266141903480001150309040000540c10400200280307260711401c0702401d1080d001090301e00c5040d140785400e000350840701003d803441c45280000903000d4502690f803280d0702081c890312034204000369900c1425050300080c440130003041c0c50505d2913050351002ca080c3d080c81040c40b01c48405220510050b5607510314181e00480c24450f4501078402105050107101c060320420000d00b41c10b800c089c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 797497014 1250 797495764 797495773
    0xa05010c02010c030e15150a0506210f04030c081b010c09031e0201050d0e01060b0a12062705090f070e0108070f0509070f18090e070506031012080909070203030f09 72
    0x186c00c802e1001500440500300c181d50800070303800041c41c41182c0d0341041c1e078842c80c0010710085203490001815201c4000401039840c0341c0d6166041203884000700d5010380460609c83c20030002480c0c0b00b0007003109600803140c000c008034944c14400d003110310041107040403884d1440c05109000b0041ca103a0342041ea9a400840e800c04a43d0000345540171300001103000c542c41d2980d200b8a20401c3d0070800103483c562000319112140348600900c417000f00b10308251110724000340440c0c5a01007112100e444d4a43c0018903241d00c4810380000300030030008107174646902410400b0403207800c0c01d12801c0c00a110b00c00860300702c1d5041c50781c09400d10890340c1c0710a5010b04414420421920345074500c43d030002071402c1450181e03040c4441a034035008800c0400841d00215040401c0f5120250f00101e90081001d0450300810740764000d000480c4000e5583c8034140c4400e1604200031211048041ca90500c1072400b41c0c141070b01c00e80840d080c00d806403030a602581000c01040300d5000818030140d4802c05000003030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 797498264 1250 797497014 797497033
    0x10803090a05150405041103041407050906131b0f030f06080d050a020c180a0b0316050f0102070906090c1214010504090201260a0b09090c10020a05010c02010c030e 72
    0x365500416209480c0684070b9001c00c420382e2a50745060b14004c1401510038044801e5406800103954800c80302102d81003986e1102001c1e442b800110070050360405000c010894440034200100540304070400c4809940b20306800384070003280e601e006800720b010b4135101c900108000029084d03c030b01044080c400c80c0380c00810050850300040c0100003158900300309a503a0040081281060104100e01d9041081106405981c50004540303900c10100e90904001d00c02491042527214040c0400481d00e00c0c20060080c005480d2041888034181c01c140105c8000540d01c941c0394064401c00d070b00121049940340300c003d000a810401d029940d0069880402c524400728800150a02c81801460b0296984941c0d000c2164010a081071301400d0144002000244c6a40c030160821412038100441c58140100c94a403401c01c8034489009070380b5540540700d2000b0382e50030b11022030329080d6448114458400804080b5400780300e001313a000c0c213a90005c41c0400d400c00004e82170b038184608000c02030740a030703c51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 797499514 1250 797498264 797498269
    0x10f0507030e15070f11071d0a0b0906040506040b180a0b01140301030b101d0702100b030307080c0a29060108010e070c050309030f010204050406140d0b090109120e010801080309 78
    0x1161340034005040045940c612200d084a000c0c2c0c0c07641c0c1e00c55041c801ca440208800d060202110142c0311f06040c448602d5a400c1141002d07107486140140d00b003d0408003003801850039802030b0341d0005c2d01400000c1c5845090000401f0005030411034640401110140002d03030845c0d0060b1840201c00b800c140c840c1d0b10204076034540a00c414171024040109400c00b00b00458250942c280040070a402601c0b2074845030000407120030000d455400c058460442c0340c00102d0420300030882d010380020f02840c01c1c03000e20313110141143d208250407a49400b85114a0001860882070082155400d24900600e107a250483d02403565000c0c0445040c044c0710b01c010803c6035101c00b002d5070b2203094ad20307294480703145c07500e000c074650300644030400d03414052503680b9049080c05601401c11200110380604c03c481c0d0328203040c08200c640701d900980010b0b8087d0740d40c000c65402e52410750011201070000400da1916101d8101500841e108400007545040b03600c54a9079103e40001e0140041401440c43d120242c0300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 797500764 1250 797499514 797499553
    0x10506030f07030905070b0304050f011a01050d0908210117010207121d060d0c1407020d08031f0b0304051b010e21060702010203011703030f06060304060e010f0507030e 74
    0x40740109521105602d042002c180884030042c07c040541c03d8032414989040354940d054117150244070740ca010418030190706c02c00381600b000d10042e150715143c50008103124000d03102090f010b60f043c0c00104088001c0c48445103417a03064103801d2800b600554140603003924020315014910741305038010300c0610042401c40440900408490a0000c1d05100c2d0407040e039001041160016030080000c03550781c40c103001642100c200f00c0d046e5955403144520315161103045000e04400650440c80d96000b08000500e4000110303085190220b61101c0560064607100400c0300c240c1044003014008801d20007000f400304816a052040101280710b0b4000c2440000c00e035215004215100c3ca004219040e2a0420007407a012080521020356400385801d0303c010b03021b03600a03c901c44401c407545008100004c0080f0a403401200400c902055030b45550082000b81d0300701500503110540ea9148802d07440d01c00344140d0761481d80010021a9910b0105409801c48652f01c09114494101811003001d5004150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 797502014 1250 797500764 797500771
    0x70e0f060f1807030b0f0303070f0b1f03110f0607050d080a02090402070507061404060e060901051623030708071205130b0d1a03060610120c030203010806010506030f 73
    0x2603a12800c0e41c028400121084000c4500c42c4160740004284240c040c0e054110740180707002682c9109039040c48800b810355034490780c000074100e45080600705001072a00d03140c0603000b02d0642d00c140d1b055041c03088042503000c0f450344200c03030303003030000301c903241282044480c54005a4044030200d00308411030715540d49a000d00e82c00c1c00e0401c4200c400082c074115080c0e0548020340c1d0090411500c0718110702c0c000d580e6207500d000ea0004110320001d0181940689412202a51120b43d64101805c50643c18441d00760882e28802d4180300301440300b001c5803603c018010b20000e009600c0194000d81030f0104034624960364032900240c0d007003004602d010603544000c48160640c000c0100400c10200c5108036502c0c00b232a50703145050780c4103020005e240c0000b0005030034000d1807140f0402114070607044c82d2012181c145500d54141d0002000a801c0d8644a010120303040003034204554034503159210722040790006045680070039404030040c801c0c16001c000701d0303014000c15541103145040200703025100d1310004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 797503264 1250 797502014 797502019
    0x10516120504020a180902040b0301150303080402131406010e040b0f0f040b0603092a0904031115010b13090504080f0f0708030c0c0d090506030606070c050a0b0c070e0f06 75
    0x7000400c00315161041d450000b441483c0c00b00011443e100411006480360b40700682c459818144601c80c64034040c8246024488008441d940447ca5981c007a9030140e8010b00036644100c911b5803500c00e45095005a4081001c0d40b0b0b2225421b00d030042c000b41c5100b80008400d07014514009517000c054584001581f128a41103070b500c11104d00ca140003a003e808025030f004d0b001039012040c00003c0c0e0303002400b44114084940c1d4010400d00c8910306d41d00501c40030203000c0d440200ca401283c04a409000d440940c00e603904262035540f05007501ca03aa000b10300303030b01059010100042c510a9104411041d80103841e0f03030300c014001030400d900e5100c141e002d40b01c00309a02c108002141e11000d40300004070f0f000c042c2d102404548030b1804030440081c2c0d41015110912a000b4000c130400ca140c030484503101a0740000300224155100c1c1c00500246410124044500c003c401401041307581e540040c1ca0002c152507541d43e07035103480007a134003800d280003a0b02a000d2a0185820300c02d210038203002e10344c0c1c8440c05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 797504514 1250 797503264 797503271
    0x720031b03220f06050c12030a0b040c09050102070f0b0a03020c15010f051e0d030302131a070c1505161a101502030403020117130b0c030901051612 65
    0x3492000e605510906050241c20070715800402c0d0080078010040c41102e0488981c10b4903590707242c0d0160f13494410484000d46035000041711102c140121005160042d43c412030000c3d0948030f403070100341119800365440005c11040d91003044651390400000000e40543c645c03055102e8a06242c4003c14001c41e45400145500401c0d42c100828040003034481e0003910903108082540c1d05e0380b6418a01580b40100c9000d25100503081e2280d41310544005d104080c090020034050040c1c1d102200207411403c020048001d04800002e40c80e914007a2521310042d103d1007443c1e46103414a4881a820394583c407580f44403900b05540c2e0340b016000010340d45c50001e00c01546a40c80781c1d41c83c00002070080c0d1300c0702c0048030070b11605101c0f01840e9000020199040075491510301c066419040c1da8a00031480000c1c0064404000342840300d48441d001500170b620139140c0c4600420310758032891a80011501030001c0300d804420048640424069136800c84150310303d01001c0701c41c1602c0100ba40413902220800d5540303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 797505764 1250 797504514 797504557
    0x909050105010e0c0f27180a0c0f0215071e03140603010b01090332061005090105030c0112020405060705100b0414070804051e01020a0806100e0d08040305060f072003 73
    0x40003a61b0400300009180c003400c00c0a4400c0a01101c1c0260b800c040c0c0241f82c183c0e4200481d000ba1a801c0100c507117600201400030789618901c0700c05400812840400681c4240703d1000d200b201c000b05601d5840c0d440c00f04d0f06903c0403c40d06880345c001400c50344641e04040821002da43c1100911094031740250964002e0540f52a43c1a140c00040c1103102c280c141c0c442d1103080740e240200d02c050103040302049202d1869507400400a85440a00071359a040c3c10103011001258052008000e50809910f400350410f0b554100144050f00002019142a004214040303e07501c901d2095902d0200b00316001c010700c481d070022a2802000051414013449141d038082000d10108100c05040c03610083e80c013007a1410f080400e00e01075007000304040d0106000001252840c40d2144180409480e81c0e5519007080c0751400030481308066606083d40d1102c0c0400011010800900c0301030300c0761712a41e140201a0400800041068640031820301204004050803500000e011040303410305144a02e0401010348c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 797507014 1250 797505764 797505817
    0x12371e060e0a03200109030e040b03010b120d08090714010e01022a0103110306060306041815051902090d1101110303010e071701080a0303090303060909050105010e0c0f 74
    0x7806003451852403158101c0e9204243e0b005040c052551031004d100a030f903070000b048841c01c0c1e031035034007000300460220807044101d82000c2d80100c0c2000c40003400851250410b8011075051a4800284616a005071485e0802c590301300c0740442e04545040000c00200e45007612402c01c00c145482c00c030341000000040b03801103070703c20010207401085d45400c0c1c54005020030b0b6030481416001e01c2c0107021a0404042488410415094911940340a4182440c50b900c9008110050441c00004c0d48652402140000440c1d041421030000581f00c2000103245c0c2410600b505000e2107885d1402c1119004000f480c080780c071049061a1b0142c0d0001ca070b1b0310700c407088000503a049030b02c50542c03000510000c000015805c0c01240240d0184a075500e5100f0340c0034140c002195214024042c0500300d5014841d201d000078441d41c4100c490600030725000907683c1d00c6081d8101503880010064409a45450040c4600044016190b0f000408084214600300100307920050500a18030045209600c18460480c80e6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 797508264 1250 797507014 797507021
    0x909071e0c0c2426041b08100207020f040204050d020f03010204091e051b0f0d02090d2405100e0c070209180f070302150912371e06 58
    0x42070750040d00a019401201c030128103501c440c26220000b070f48060040302c203019075030000d10005041c42082041d85d860740c41d01d0b4012a4101845055000c1d121000038005406110320a082a100580564ad940c0240108000050f840510038480c5204001c2003120b551180716042e0f0280e815103500c4a00359080300041d0090240358081c180c904c1c01c1c00c214100c1002490052094907440c9102080280c82e0801549102c023810b64201445601c10007a00441d0b074643c00103400100e00d100805031a288038040828040d116054048842e429161040c00295401d2200000405604c1d50200182d1500404211303c40140d8400c0036820a0800e001c1032008608000321050030b60080e202c1c80b101e0409003d00c100f0740d015410006100c6c0036454460040c0da40101c0e4413401c0f40d4005000c03c1d26034140b680940740690180c19195801854500b039054551000c1c8910015021611411600500d06062009000f11640c118900c12a0744020300340c0065a00004110403030000b814107074003c9424036110380103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 797509514 1250 797508264 797508269
    0x506010509100608090f0613200102060c070c1e081b03030406051c02040b0c12090f09060f0d030315050909033f04120201020903060406150b0f0909071e0c0c 69
    0x1038024102040390014810f509000003509c80c203240e241c52841074111880142c3c801c5416401a04010085410040340e0405001d03900d002d044080403440e5030310b103c10101400303000e0840c0e0700100c001c010017440030140712041c3c5280503c507050f00360300354103000241c42c0d200d60302941007442400f00b0302290400032000c00000e280700104003190359039119642d0451300e0700003c00001081c1315100044900c9980101030300e04d0410b000c1c201c041c007843c9a000704400c07403a0003070001c0d0300285100b508070000d81d60381720024003c5000b51400100c05201202e01c052600c11504a80e0180d03409105100c4d03401000422101084680411130391180e80f0f04512840c0500c262100c1c200d492124484d0300d48101a000b41103005134450028210040c8649205900340e0047e05d10301030b89900610700060203e070980d044020394482003c8200c07110340d01c815641010383c001c003071903c15a010100d42c080b40360910540c142c1d001021b41c100020001007080482c9440b11070104890104078181c245c0c281046030b00001e2401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 797510764 1250 797509514 797509543
    0x1170604050a080d0609111308030c06060409082b050604110912120c0309011205130204091103010c020604050606010c05060703020c030f04120605061926010903020a050601050910060809 82
    0x44071030100c0000141d8202c10304801c403c007425540027505480000131207098050107006002c0035540c0904000080c64011000d40d41c0140070001c8500c2107071442c4c174100c15000c03e400340b00d076a00e40d205141e0045410003011103000c1c621b070240548034030305400c081e50741e0810211070300b00c804410802c0e02420000c42d00740394419250046a4861080004005840c400e5020780c2e4401c0041882101d80040e100c06449040550490b2000140036080503084280a43d02400361101a4800740000c070342181c2e00c00340c50390016040102840300300081400100c0d0032500920700948803600da529507a80b0788002030940004e1560000700340da0034040034425a13826003d00a00c81341c030f40d40d5551224001c24000301d030032607240c0e14010000310f60b450010b070116016014003480c40f914030308043d4030380107601c540702007044200b1014510812815013400f03640005072007603010344120901442c00e14501001070300103d2141c9900307420440e202d50030407080c0046807020b1030071481c9511000c1c2e900b802c0000602140b003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 797512014 1250 797510764 797510771
    0x3070b060a1d0118061a1e03011205070e04021f21062d1e090603140706020d0503070e061b0c0a08160b09220501170604050a080d0609 59
    0x1120710548842d02c0c2c125160100b42d400c804c41c807055004200c4403517000e100c80300943c40300d0030170110a048000d00200016000c0c1a03c600b40e940107940b201d1b401c26031080c001d85080c0d00c0c0c4441041001c0c4000d1008001090082116040550002d101d0102d180100c268801c0e0b0300c20a580300b00c0c403c450b4017614507941a0200c5215500f806da00004c1c00c918060b034074044402800e03020010580302c1c0520756502c1400a40c6031010300304070901c0000d030041c40071071030502500380002c02c400001380b2a03007008610449690140c41c01c6008010f0800500e0751104c020354001c1216180240c0e00141200c1c1c1c411458900000c8002803070340098894000c1c00303418054603120a030140c0740e850b0001010140c0e1031080320b500d00c070b079941c4200e555035511a00c200450f420401c0f074800c020700c911140c082e10b22020010701441072455607001d0981d20503080322200740a02d8440c40100031041c844409a000039400301c019100ca46000d85445595100c07659000b024040001480303035540c00d0ba6807220020b0a0041c0341407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 797513264 1250 797512014 797512049
    0x612070b09012d05070317040c03150e061305120f09060306210d03050c09030a0b060a0b160611090303030f04020f040c031506082716151106060303070b060a 69
    0x138090742052008901154551000004c894136101c081841550b21105864045082d541c0d0540342902c888010040c107a22200240c00401045c040c492003400c50140d0f0307280901c120b0800c00d1822400454400c2440f40c05c012102d00440f104049800d40d04054940d030340e403070301c648010400411400c85074821039038612002c02030282c0c0100e1121b202140030380d01030103961140402d4884901c59400190750591007000d10000048800050643c809002000544a195244102c0c803031540540e1024204921045400042011030310420401082880c0001d0500c0d46480201c1c1d88c03480007601250b0000f4101c0300207001c6554000d07240301c0c0e8200182040c8200003000c8c0c0060047c1501100e40c42161445281c0400c3c070a200c2c104043c4140c000b0100c027a403807006a01c0040c0d440700c0d00002d1480e20702078104042402c5040a012a00030f004240c0440008a034007a801814001144611191034101006204540da000000c0da40e096400060782c004c2c54490f0340015040f840d040e071011640c4270900c005c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 797514514 1250 797513264 797513267
    0x111504060209090a05010522061e03031704021c0f020a17010608010902011b050a020d03050a1e0f180305010608070e0a0204080d1b06050f0612070b09012d 68
    0xe44001c0000f51501030607501d4000401c82134810900550703401c5824800c8840031511041c1131441a080103800005584c1e4540d10003039041c07c1c5041506100302402181042003661004440b03004041a0810101c039060030350010700440921080700c0000e504940d02c4a01f4815660a2004020342c003c100002030396503081c0c45064104464500c8003554030340b140005080b60306005a0321619416036610910f5480d070000c1081d2201c0740c1c60144c031a803164a840360300680381d1981031071100307004c3d0300c0321a2a07446d6100c008264102041d03481030002600c006000e4080e402514042d811020b9080140c1c142000030b108400040c1c0d43d600c050718a40c00d10718005150070b00455104151500010b05410f9559841000b609038481c920500072194480608000e00c4c62080303d03058408020034600e02192030707030703503c900c0151603050b80e2400703040052109012483c6401440381d8141c980b03201c0a410001e1405441c0307850790044130452418800490106c00348007007203a02c0101d121101c0b600c5820161000f074030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 797515764 1250 797514514 797514517
    0x1c03020c0703350d0c050d020d0f1b0c061e02120907051f0e01111c0e030115051e030a121722021c050c041b0504061115040602 56
    0x900e060b001e0100f214016880c001c512141c03d8561050501c91514414400c1880209840000401008000d221200d0a070b412400200700c0780469583c0030500107071003503114084890462420600c0302544050407d82074000c04400e4071143c0114000640009003040600420b080505040100384000b402c4000801150342c500d015013150f01c03c40e03522a03298003e000700000308042c02c3c0c8440401140c1d40c09224440c603032030001d0380c030180340c041c0c1d88420000c0404d01e019164050b507200070090a2810301c40390707400500045211000c034024414585800c03101400041d6601800f400740719803601100b00c42c0310950b00380500c03a00c06401c982006030507080c4100301c8070a25504a0000383d1b401980100c2030300142950f40500c1030a6629500f19030204440341c40701807134420403a080241c190600529480d0f09046528290143c0e000e000c52201c8042008103c3d000c030010f141020140300e40840c4101d91001c180d4081d030f0650300385025000140c01c0c00718501402e40b584145040c0c0740c1e030100001c0000c50340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 797517014 1250 797515764 797515793
    0xc06151203080a27111302030414210a18031b0e0601091d15100338120a0606090905010c020c0108270303010303031d0c031c03020c0703 60
    0x5208010040400c500311540002c03100803d2521350120700c42074040b4030200001070401c48006c3c440196007072912007000c10390300f088078160752081d030759060045030380410b1112030075580550340301e2040854125030700c0038a402880f0f0280200b04050259144440c00b9860601c00745401149441401c2c01598465200046600800c83d0004044c0c000c03800a50003075042c14243e92205448400304c1c6a0007543c01520100200780d6800c6000038219441c05860307000942c2401d62a0f0369000c070314031520903907800d20600c049500c01c600031101d6468005100203030290702d544040440b05155416141440d461a00b000e40034060301c1e140c6404400143c2c642e10b54090305213184514000e00090480da00706980341c440100e185804500040002801e0500c10440001c210000302001e509e0401c2d21905c05240d50000d0304211b0110350b403a03106040c1642e900700c006451034a03041c02811100d800c80b001c43d8981c2c0b000c0365040400c40c9949840150791780260107a46074460060200c900300c2d9a241088030b0a00c4c03955 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 797518264 1250 797517014 797517031
    0x130c03150603021002120d11090a061805091306021c0203090d090602160b0903010905100b0906090411040b120a0507030b07050c031806090904030302040816060c0615120308 76
    0x1040130f0082c55001144044039003080c05003060030310090b11902d101400c82503200701031000080003111230079036034103034114040c0c055542d130020b040c140c0c1503048180705240c0d00700c0351003160a0010040101021500700200e5035002401584170f8082c00c0902d01c0d11394401204803602e500100801c8000180000c00400c00000e6130b440340c0125640b80c0702030380ca0300b407410701c1d00c100c0c00e014075800e0008801040080003000c402800015808216407166414218810005074165441e01e290000c0c1e071820b401940d800c00d01c121603490301420560384e4115030480145810b070140e621b4107050f00c4265103801c148403000740c5d88000d650000401d8580240c5070781c190b0004562208841001c605d04601c42c100f030380d80c2140c00000031850020f113030002e214801d200b22802c82e0301617010420207006442c0c03c0740450260b40300391000350319241402411401c04c41400c20b01c41404600303410800a4030b91025160134002d8104000048a04a014040204002c0c035000256860114025401019403007500284203c1c1d22 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 797519514 1250 797518264 797518279
    0x207020a0608041104050723030a0c090602100902010c0218061306060f05090409140d0f1e032c03070b060405060321130f090b04050c03130c0315060302 67
    0x2100c0c016148102e054502400d405441c400032101400c166014075000580c90515035405001607080a01d4580303c81e0b1414031300100401446803080590084280034001420901801814100000d5592844d0f1550400c07113030700c1b2803e4200f5079000e0700c841c140060300900303141c102c1406a004480ca554007503450f80d0041110940424014400707100d030b10140c0300319581f803500d0390340c1106084030305801a080040d8016501c8518800040f08084196000410000541500c5480c0c2102500210348115003c0901921403056146205e500c4c0511448000500b00001e05182c3c2111140103420300352004980040d10001e00c42c02c0050000203412024800c078441c08035a62490184410f803002500c505805510801502e0100c2c001048a201070302040c9001a04052100e11140750140840e400042c240912003001c1c0448040c0e07004404084c0790645040c0030b21301300b52014a40602c4020040c10700a40c0746595901000603a00c00352000390740104c115240c0360070342d1036180014041480300701d210300e88 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 797520764 1250 797519514 797519519
    0x6020a0f030b100c05250611011a1002010e0a05061512060a0c02150f01150512070e06130b040503011d030715060503030307180801020c030f0d09150207020a 69
    0x4240070b4000281009041e050842041c041d0903907403401141da007201c107402100b0688440004400e001ca085000e142e14443d03149141c010301500040200c0e40604a99040c40d541d001039820311500034103156016100302c401545d1010080703004082c2040b400701315005150014041c003034001030700350081c0003003040402c514070b88408020344040c5140c855502a00a240042c4e843c7ea15644800803011060058403120380102c0c81160300c01004803008400507030760300010303c1403008005a00903417544600b071451520302041c02043d4040c0e401407010b41000412040f107841c0391030700800d55441c4840e0b0420360300ca560f200d110044142c1c01030b00031303d8001d61824100c801c00c07102d030f89510302448141a011314607100064407641d9010304109038004500d41c54640c0051a074070200029031290450b40c1c0c2c2c07002511114803445561490640c01511180c3c01030120700300c901008000c941112051442082e500d840001000d00680794211000d45100886801c410900205800801e01244215900c4c18203d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 797522014 1250 797520764 797520767
    0x11a271207120b04030302040509010603061404181202160e0603010e070501050d021e03150910140103020304170714061012060504240209012006070f110a06020a0f 72
    0x14000d100b181d000c01003031041800410380c010000340e00b0a020303240141c6040c0d118004140700d40000e9100c6000a0b54401d02004150750400306271010302d20846040c001c011050b08054010342c003641f0007400041024071180280c1d40200b28004024409228800c8455668020480307480c90481e1085d0195082407045c140030400441c011054640c161541ea0900c80e01c51b8001c0000e42180340168108042d12004036125403505001e1071041140406410380c00e41c3d4181804a1294050150480030310011402d0100801140381b100003003000b0329005031aa03590b820401c4001c0007840c0c2008501a0005500c0c0520040340c0c0c1c0f0103611145c21003207452035202c86c1403042a8210501c500d03800780060b86031a000049480d0000360304940180010320003000f0001e281e00302c43c28446039070701c5401c0d80020206001d5030801085e804011100891030050003450f0b45440e21341900401d48810800c481001c00380490080003135110390042c0108031341c0d606810386011130007544a0020030004c205010340048585 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 797523264 1250 797522014 797522023
    0x1090c0909063015020d0b0301060e0a020a031b080403090608060d0204020903030d05011e050307030f020d02010c08030a09170c0a03110c090408130605030f011a2712 73
    0x241c100c400306540c01c0000b8140b5031183d0395039000803d50814000c1100d004112546940544d204c42e900d40141d54000d406046c8049401840019000342d04000e020046081c520030780720b620502e002400f581e9607030461421002001b4407008070f02d2040201d03d0781ea0019a0000040f0712070740c401d4039402c01d4540c560005803080e210483e14280d0290502c80d5203401400d250700a81b5150380040c040300e0605002e0150241903a002340c1004019103801e0303804000c0300c0303214041d00c2d004003010350203480c0702410b40e21055815800000e000e0300401201d4a801c04591141142001a5400081054803814070100201c00b030002e401d0240c6180c0b9460881c405107810b64001c88041c50300c114010f00c5401000d0ba0180c0c0c1244000503007030524025564040203d40f5a80841c40c4154824204595112429840d901c03404800e5084102080424020091001400a8224103403001804800501c000c03507115503029100302c4648000183c0c0200d2800300001c00c4480c040148901141d120100300c400400c000c1d1348 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 797524514 1250 797523264 797523269
    0x70c0611060f04080a111c0e0a0f09050c0405180a2a030e030d020c011401090902060d0917070312050f090304030b0a020c0d02030a0207060e0a060e1801090c090906 72
    0x220b0031014049400038441d0341c002d2002040790b082901405c12400781e114101110702ea100080d511540480d4003000f980841c1c03500804c601101c2140c840b60518140c1c0b08000d00f14020f440c401c036a100042250095520151001010010800541d14081504c01c0365030401c1602c60a500e130f401c00903450010484070311013940718851048103584440e00003c0480142c0b00007124002e1030700080018905003049400144500c5501d4000811210314030000c01082000c144c0c4114040c1c6c1c940b110780e01c016036401d81250049507c02d00e01146104450408003003802d103491000d01180c0b400182a4105608160910250035901c2001c10255a5603441040c1141c0d040304d6024040e0010041131000601101c190b40c2c00203034201005082211414185182c8442e0b0707065031001d81e00200300e050006a0400121010348800d26018082106076004201030510a000e0703c0107000b0280007031030f030b07949901c2d0803841d12080d1040d81c1d07a00c550b07450089100401401e01d403c80091241c21010414102c24000d0104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 797525764 1250 797524514 797524531
    0x70803070c060609021206090a201e03010b0a050a050f0d0b100c020306070f09081905060c040b04180b0a0b0408120315090405100504080301061e0c030503060d0503070c061106 77
    0x34941c7c0340c0d030401840c100700500c822081503407400c20b03149403100c641f04000710f243e0544810703964000d80b03082030035070200d42066180c2d41e1004200501c040c42c108000d030b440600441c1440fa8441c008180c1c10384160048180035a1030000104180f6440c034400e8010ba082000103644d900c0070313041860030854950001c1c48029400d130f03100710041440507201e100f603004c0055091a10700140c0740c031203402600380b0004864043e0440d41e04c0b422002445418001150090702c00c45000340f400d03140080c00022405103100d401d001c1081c0211b000c170105001e40100c00103000007880f0240743d94a50680302c5c8540c0007401510400c1c460250658108000d00003100c0c059085880100360046500080040108004204441c18010b0000c2c0f1a80340d400e03401194041ca114619041e101e6040020050401003040c0c1d40c1400545280150108550400061803080380c061038403941e41e5846001190380c0c4078408400a105100000e400e01c144445e203d80c40b019203031320340c0c2e58100030002c01d42250340d1544152610310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 797527014 1250 797525764 797525797
    0x18010c0f030f0524180a020703170712020d110a0306080c0609061225020304030209060105120a0e12040b0310050109260a080c06040c0504060b0a080c070803070c06060902 75
    0x4c190030100d4081000d0100c010500c003080b107080900c200501d44240c510801050b00420410100358110074044c000104042076200e151030803070741c000c04020500c1c0440c68900c1d070000f44504c0031001074201c0141101c040a40a42d118003e100c014018880340c4218002030151107240011b620700b02048410b4004010449400c2000c1c0b203540304c90401010784103100c0e400d00507861300c00250314907140100383d0455402843d1590700c0c50050001c0040003c11080c1003040401201c0310113207040c0409a0094242a800070784904100640d40c540707602d98055000a010100e0300280c181049001544243d4403030f000d1840c42a0360388015903114600703002e0312406141e01490f4030080300c801180010000e040c28201c5000801a0f107809805a000c0d502113111600203608003c01d001d5030020100086c04103072003c1001c0703854803105840d1070003860222001c0107072001c0030410780311240058441d6290042c0c90300c2da51f804e00d48001b42040e15120000c071012800c2c040c000580000602c26641d010700c1030070707158 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 797528264 1250 797527014 797527051
    0x151416060b03010b0d08190201020406080a1a09091b09090a14070504050103120f020d02071e030b07091e080304030f030512041515030c0b0318010c0f030f05 69
    0x6102800041d04001e81542d40c9032440708450380c5080303a050010340034071225a0785521900d00114000241950041560b0040004102082d4040d88503640b0042c0a080010b10400c5003c4161b94a81c00200d0681d0000015081c00208640800e0b04150044009041032585040718142300380d08000322414200343d04204900030204240503100c0805403a15425a4134144e10354000400b10740c1c00713820540c0c1d14441001e89141c51031f000680007400140c1800141000d00103410000d40c0d03441e4030b000f500008428440c6030991500c4100d5948099a0b1110356401603140180c4020003c540600c03400d840100d86440320358081c490f054404041d00e01c01000740d441c0504503181e01840d0341681d141101001410441d07880138002d1140c0960180d0301c138074042c840400903000100e05803000032000d01d91050904908000184010006008a41d25010750030340b00d0f503e040ca1086500070b040341c0312665508141d403448c82c0503488100400015110344041180c020300c28107410807103500702c5602000000e411840e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 797529514 1250 797528264 797528273
    0x1409190203030703200a0c09050604022802071a1812070b1e1611011b140c0d12120c20190b060a140a0b0a0302090a151416 54
    0x10100740045d1071078001d042c0f4140b0262180f50450205017681c100341820002e22030010302d401502d40081003246c082d424050031181081c000161040c4800d05514400c041200320750080c40424010241042c01c104508107007891400c0c180e0000c2401064100c404045001d42d01d40030881504103001c08000b020101d061404000072640302060540100c03145100044840034828002c1a4030360f042694001d0b150700e41d00d0702400a03460102d91a050118100c4030a5000c02d0100740c1000320364002c4000c0410804001100382082d11210007036800045000c400f1303040c8100e800c0981e0810696950b0307000a40402c40c61441290240b01842c0002482a6402c0d204a0320b416510800d10b824481a240c60b180150745049240265440c2115141a1401040346600d4481710100007001000c44091458107034400103100ba40300ea0184640c941004512a0000c0d8800e03030507a1160140589100149034941940b1200e1128040e0080c00142c82c0c0a5034007140c044440640d0204080383e00005006030300e42c2c0d00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 797530764 1250 797529514 797529527
    0xc0303050621030d0e01020a0e0f13060b07030f020c0616030e03070906050a1a0f0d0204150908010b03070e0c07020402070b130c06030606080601120902041409190203030703 76
    0x2440da2000e80d0400010801c049088044a282c012000031561004a2168041034071001d0b48000201c0c0d10500c048411160460340540503100102e03404078260514000203a81000210301c40c1d41d0b4986400c0000c110b03084004010010300b4002e44450710ba6201c8802c00b00da4962a480341590012002c0c4402007428600010b0001080d02c60300742000c800c224880401d1400c0007a074804040c00d9202c10007004030741840b0180e61701414131410300200307050200c0a407071190711910f4500044000c2c00aa03110700d04031140c2c15036000d4a03a040d9000d62100e03400368024000301240c050495076500e41162045140380007d612801c5501c1200b0180340740c1d0b034881e209011030304141c500f07a0f00103400304480c00000d030942c5a0b5612849000c2480c8407084401c1c208084c08540fa5004002814548182480415084100c1580c0b201003403a140c0944011400d0160184c4921034000f500142062510840c0c8000407885c6071040140c0c008403882c1340900614050320035403115001e50150010484080440d20950 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 797532014 1250 797530764 797530771
    0xf03080715050f180c0a0308090102030c01150509060621070c050114010e090601060203040e04080f0c01291f0207030c0e04020126070c020f0a090501050f0a03030c030305 75
    0x100c492078560303085150041928411107900144414110400c003e44000140001d85403020000034644165104042509089140405459090040360a69840c0c0c8200100c3d072081070158001c0c0440f0940048580380c400c55400703064030031240c3d44000b500a08101040e901e2711103180d021318441c405104142000980c010300349070b00700500101014041002400742503111b5001100e520195071400e4201e61184901626409594102c1001002220340c000143c8042e118407402c82c0b001625940341803449481283c0384044003960114102090b000306501403c80c1d07160f0401000a540041801c80d101c03440c00030800c42e8810b40107070503810f03000d844c0b0001d00d0803400240112111103440351150118428950f01591500e03d010080000f103590241900c490088042110400c8194100d21480c007160014107000400400e60002025035548040c1c0141c099001b8101c1244203071541c8118000d40001d009941c0209060401c401190070080031203400c0b0f80e0190b643d079602540941d002c074094034029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 797533264 1250 797532014 797532023
    0xd02040b010917031215031b06070b0f1f050a090504110301091202010f05011d1e10081504030504031b180c020114281b0e0a0e010f030807 61
    0x42c4400704402501d58901444100c1030b9000b540c42c3c2c1e1120341c4016071a000107100003041d60145800301c10325140007990284a540c824403900c54050064045502800343e01401b40001449000740004030b00410701190081c0c41803031454000710441400140d04001910078503030001d070008410000a00701e64081a000742c402c0b21240708110075a00040e081d10a082400d0f41c801c1d00241002d0901a024401c141d203070004144140141d616200b0701140010109d414808840d0904001940111070702c103003544442c1d80010f03031960f1030800c40480c000346040d03801100000c0c45000341d4400c061000d05550752040b589551828a06800d40e83d403003041410040d48202c90781c55078580802c82104a004000a40004220000303966036054002425154551000403a0707815034014444280c007a5001b070825804081c0014240707415807041c0400070840c8001c100e200003140072061805507840341d80182c100300c003210a80021034441c0505900c2d607000b0310420082e0610490f0400021710114040c200c41c034041d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 797534514 1250 797533264 797533277
    0x1801020c03070303050f130203030409020304080c060405010e160b0307050c070801050708040303050a0507171005040501140102010606050f2d031504050108030906070b0a1107050d1d0d02040b01 85
    0xca280d0b800c004821400f20f52034100b04450711800c00e5801c3d41c4000c24041e074684a500540100382c0324852070180043e882e800000290030301800c001210385640e81c0e603007200c2d0145014109140203000380142d21069005440c034140a22110842800036101c4c2644023916640315a2011340d60343d801510050041e000d0081c0005070f110081c45850710a0240c0d403a1000149410316000301201c800801c42280c90345032500740030400e41c1c401c614911000680c1803030742081c0c5807181800b0b90066507a00080c0d101d0b041400215940e8490100070340d032040203030028000c07552202c0040e920307402011450007090340103100b003125a48001e114910b0070744405000c19041700c0380841e1036040342e000710307210b070159160101c1c0c3c0409420241700d65401041880042d40c1040741000005134280315142d00071340403c0000001c6141014684c0c0421000c1c0d100540703150796800c0d0351502c84d490b0505a115140402d02c03540c01c181348443c4c402c41a0248010080c42404a0942a403c0000a0080c43c2825041103030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 797535764 1250 797534514 797534527
    0x606061215121a1f060c031209030e040204080a05190b0c0901050f04290a020d05070203150f150409020609091b0408010e0c030304060e0909120a0c05160509180102 72
    0xa0760800c2d80c01403290003d104c00c000e00320b1880700050025036010408009114448101080e40586041e030700080f40407011400d002c00d41801c440501800700e10704e03401071000500240f81440000c0314035071030748103000307403002100d10100450038408c804002400c040e0001002a0b41da1114070010924500305060035030504020400750070981d0020703045441d1203204a11070f4801e2215407030002401c0c012074000c0d5446e14a081e507000707440700c2c804081c030301c184036000c215441159000d0003124043c2600154060441c644915410358a90066840481e1141840d00100301401e0074018284801e4004d0030140c03920740c08005000100380c0c01096849404406414040c81d404070368020701c0103201c10030020614200703a0740590f0a1050344401700d880390340100000c101c1250082000707141c0b000112002c8240d640d40f8000036041022000c004e403d030750f500081c014007403034002030041040d038041c100310343d0810501d8210a0200c0082e0044942c0b040d0341c400000c48081c0c1d20b0a001007003003000d000141c100300d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 797537014 1250 797535764 797535803
    0x30050f011415030f07120309091401030b220308060d06110c2e09020d060c031509020c061503010902091003052503081e07060606121512 60
    0x40011041a07500800402030106054a2100a11001c4400c50152100c2d8503d5800107685034070700d200f03100d81c001c41d400300c0c1c5040c50700032110304c001050b9540c4c05008441480b862841015404d0000312290001c1c507000c208125595840c42c0c031b901840760344000c402009920b05481040b402041c6907441010a208000003e590b8002c2c145601410200c160700c842032441168102105001c1418440c01801c0104400141a03e1400b0074100e01707403c00140f0190500110320900411070014000e54100154403a030581c4c182e0207010030580c901c6405569070744840583d0268800e040040380654046804035041c1040140d084130384110080c0001010300e840da003c21044501110036031011190114100140a0700344070080149001451181e056072074440000d500c2005400081d0401001041031a003400030381c09440b02808170340420548403803451030070300040c0c0391714020140056030b003c0811051120500400303020300c840c4819142d040707040c01894030100000880030380b0580c40c1101d0303565554 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 797538264 1250 797537014 797537021
    0xf05191a0f2104020f0d020306130503070b070203340201120204090e1c030608060c132303010609020a0905090c0d0203101401020307020105121521010630050f01 71
    0x124102d90b034042c141e02d0700740100410f078500b0b2841d031801004041c94480040c0d5009c2110340c0d009515800c20002300702d4a0429601e0b500914a004140200c070505100360550000060301400400d00290010500c080b5000000c0c00d0302d580c600c040400c0304800e030000541c002e03181500d03108500c05005040a43d542c1d003100070340b640340581408a0700641c0d41902a0004100b0b480070403683c078182444603520317006909545980040500090443c045142504403525800080c024149030054002c5c01408071200042e01c6481031682d4860b40c60304000007002d0419009440a640144d112010680e00c4e240078410407030303030040ca404102d003020401824005035500c00b45001d144030341510740f0041d041071200600d54031504003050544d441030000400503a0700504588001440c00300300415030319050b071120300041134500e0903940001403082c46034031008040f200040b01010700f802442403e64503220031024075480303510032845070781c040180b40d1040c4043c182da0098500c21411520802c42d00311030142103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 797539514 1250 797538264 797538307
    0xf16020f03030f0901080a0605011e020312010b03090d0906021e01090210050918011a0d09020a030303051f21020d0b0c07060b0303130303031a0a0f05191a0f 69
    0x10f002022400320b8040d68885200d650140d001c000400c0032505280000c1d00c890704007861122021412079150089920910a0710f17400c030480da881c10440c1d40c6607402501c03143c10803100d42d0b5080c401d00d012171440c0ca01c990f19010413941c164004d00a012100e02880d811081100c5139044d0640d00c81e4405801a202c00c00c0410340e090455682c070b916011401b0400010202c99030010200d180340c5801442a4a080b20380c201c031700c80d261000655200c00b101022806000fa280001e5801400700000000741a0940c01c1103216006188640c0e4105218036074042c0d0641a9008040740291000c00418400308002100030021b40028021442a1065502e1074607500c412568560100d402184100400000f4000c5043c1850114059820300b00d800d01a5141401c0a04c4003500301030704ca050041c081ca030141400800e40401034074146800b40c41e47c1507103001082c58030649008a1000c1810000300c0750301c03001502030b648108480015900e5801094007150040740d2356240199081012200305602c040c5030803213 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 797540764 1250 797539514 797539537
    0x6010809120c06010302010306052704230606010f030e030f0a030b0a061805010507030804020d15090f120e090c03060604090207030e04060b090a031514010f08070b0f16020f0303 78
    0x100344d8114400142601c610398441c1d4015040c012201c0f10184003079414140a0f5410200b100d001ea9403404c142a03900007040a8031200c680809042c1120800429068400c81c02a2600c0b141e00704074900c21001c84031501c1e110400c50b041800305181d00444d000003041581e400349000300d944a8004001204408154080e00c08180c580f0203200550242e0b0b150b560041070242005170400c68592805400894000d0000344204415020b030010080c0e54a859000c0d1044000300300920207203031034086040245180e05407100d5962000401242384912062021060054651045911100e0780760b8000c0d0000b618803a84041e00b8040410b0321515440945403d0380030340c6d5881c80c101800001d000885090340c02c40304104a08004090854440b100488101d075417011954081c0c0b004031031200000d200c1c981c0003100c034040e62000090300ba4482c6070300805440110058504c1c1c07564912001c00f2a1088d5075204000c007105000e0f080d201540d801061191500180200d40c5802807040005d0071907111030088171 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 797542014 1250 797540764 797540773
    0x23040615020f070501080a021309111c05280b10050301030615033804110306130f0b151005032a0301120201050408060a050a0b041406010809120c 64
    0x1090035410481440200041000b50901d1402d04c400200305600090000304415000500640c1d80c003a010300c004001c204030041008528094581e00b0056482601180d5580160a03d00380300c81c071882c03055038000c4105070622044031490080b03041d4500d039000c030044c8002e5654810307400c1c65112070b012900c0422450b500c0035501e6046141c401c0444107454003684c015855614148001030040c550441c8903141c1d15920018070501000300402c3d6561070400c40702c0128110184000c021422002d85080c200490555945540f1091100010460840040c001c040c0d1411102d0100700c0740e07801240c00840078000e003880c0d01d42d001d01041030f942d280100704001400000401a403020f01e10800050078481d140c6c41404008401917080c410300041c043c105448011013500021a8040c81c220340c0200005070541d032032413500340b4004004203c115800103046042c80c00c5a0f00500e400d00c2904140d0700104004001d540700c8500440e1240c2c801041c10710203200740340c10703a00fa080440000d002c20303070400002071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 797543264 1250 797542014 797542049
    0x9071206090309080d272402190c05040b0609030f0f0c0a0323010e0d0c02090c0306060a0c03020c1305040c09140a0e21070318050a230406 61
    0x10480d08142d80440c42903004a105401c106078403001c0c0d440e41d4020852280d10b42603006104500c43c1059a107c0c0182880d44010100080d4080001525244264082c3e45040c03481c10540300b461402480c0050542d00740721010b2207149440e900c82c00106c50080c1000b0701702280b20340130a140c040c503452038460a902011210150020410000b0704203007003900c0c40e1400b285959503140c2d00c0d081032289a040000d103240c140d1111a803d500100f40303456404200c8e1100003007107074050005d0240c0790742030f802500700c48000340d05070840b082140c1c040c01c40600f6172403424144c008102c40c0103070714620441c11030095909482141d940d540c40d40c1038425642d80b0018250400349001c240240169022a44031414290f031000201401c0c50071551000c0710070400b00340d0304026070b402c5060410140308201d4025512000c030390b404460102a0003010300c00d89401c5841c00320799100c24503510b114414503a011040240c18456441d0000b03e003030080c0c43c52980000340360f40300e01c00601520b4241d0800071440280c074044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 797544514 1250 797543264 797543267
    0xb09030c060913200f0c0709020a0f03050702011e020406090512250f0609060e180a090201031e0b03060708092107062d1103040605090712060903 64
    0x159032504000c54209260450180100341050700319107000c010155901524409043c004028001a903524a9259038032030303c107010b81005400244022210707201d01c0c10b0104031881144215484180c00d500c07561212001402c0407005000001c100030115500c6001c03d50350800400c0418103a48e6074a03c000d80c545080c21002429401180d00ca14458094113605070202000819507801c81d050400649182010b1504015a4042c43e9801841c80e55002d080000340e541e4070540c41300a4030700c10342d41c40d000010b0341e0041002d280c6011000e0004800214045110780d030541d44015003152040c100800c2d0315030082d03100c002000c01d1000784505140c4840f088500740c0b0302030089580c09011030501c0522410310b13140842d640d40d180d0480d84074000260304825514071001c016584210741c442e005201038140062240a50210305950800d40c0c900940700c030000101c140512940304110741c0b41c2900b9666942ca80801034000585031004a009200300406d406041c8080280d1950081002040c10042d6180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 797545764 1250 797544514 797544523
    0xb07180b0414011803020f1804050114070c03270b0c01090b07080411240705011b0c05030315040b0307032402180f010e040914061506041206150b0903 66
    0x1a160400a105203203c1400c40c81c1850310085e01c0c2c040c0d40050100c505400411410900c2040240d070861960040000308030054000c000070300f00c0f01c00804001d4482c4d0301705a486070605100140450350104c01c00d0003542000320000c0001c0a40054080969616900740100340e105010010059441d034107154140540e01c2400d5821181d00d2425603610300c2d00b0f0321181c506440c90b4039003500c01d6040301c0c041e018038a140310401701c8034000f102400c0d6548a880c50024024040881e02280310101c01603030002950087c003101400c0d5803c04069441c555851804000030308011484075031260380d40911b05800d07101080854082c6205507101041250120002c10558900e4511484007a0040000700c050380b0002002d130342c2c0a076081c0c5040c0c1940500000596010002005441c0c0052401c1030640511100024010503003c44500751615a210090303040d440d070994510300c94000c2d4040000304180c1c20520424180319004040c001070030300800c0c4081494081d581e1009001d0080410720704142e290610 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 797547014 1250 797545764 797545799
    0x10c022b06150506070803040c0b181e0d0303090c08030a050c0708120409200a0201021b0d0207050904140304230405040b06041113120c0f06020a0b07180b04 69
    0x1042c482e01d40340c0400140144201c2a00400710880800410104008040c103c0040d0940c1c01c0300c1610340410391100038070070706d030302004510030404450030140300300300645025003055014140c1011030800d600c0542c060f142c0e19108480e4640740c2c01c00000c80e154140040c0000c0c4440d035a4095554503100f481502c0d0800c907800120040d0401d0b100c0031403414200341200c0031500011004580b00040310740c51050480e10b40c09504a9100019462a030158103600800e004880606240354035071081d0804d981e940c069413502c070003581c07000c41e09000705d140400e06164841d114007400d0180301204c4d120f09040d50040e40c090865511106403001c3c41d5a2104101d0703504040135603040016103880e40750000e1814020342010702955669042451092614080710340001064901c2c440c1240ea030f50041810385000f0a092b280c640480402103444100d0706015001c0350340030341c001c003045170003511211110480900800140010a000e030290a00d07681d140000915140e2140b940f03640c60300d0940a040351548 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 797548264 1250 797547014 797547041
    0x60102061e0109050a0209130204060311091804210e120f0c101416060506062d07050f10050108070e16020c1801030203071211010c022b06 61
    0x1c11030204185215400341c1100c24120011419848184c1900002d01c580341c03000b608850094042517800640c0d4008000321078003075034100968020700d10034540c1c3d40155241950310000384c803a4070110544070942c0a03001401101c2800020548020401c8406070380050a00403400340c1400010030301d0310140d00340900c3c4100026202d5496248807054541c201c01c0000c0f0b03ca02c4485015102d2180304042e003014070040d1025440c2d4035000d0000c4d40080018204040701d01c281031a002410760f040010540b140102004003000c440b0000100b80104551032100000c1410424480316002c104100203d40000c0f9200001d0010001003144c0401621710503003007252503a00c028000c10035040010354166000908400e5140c040c0d980e0513040781003166100e24140d01c000c035045022094074101544504881c400c8040f204440c2c1c5c0c612014488424144c4080c0ca151103011260310f1550103402c102c408184024624002040076041d050142240707071141c1048850f14810010400031640300d040310b402000b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 797549514 1250 797548264 797548291
    0x20103150e01051516060e0c040614040e03070302061302040f050123010203040501022e02040b0a09080706052203120e180912071e11030d03050106051920010506010206 74
    0x1764084c00ba5450301303030800108001d0755007010003480d000a0228608a500041003441842d540f4810152501c1d03a00a500b44a01d242140d00405d0036400000c03100025415006011299114120000c0482c00100240c1c1c0040d2942200003180e265841142d02a20011300380a4411100c00021a100c0d40c40006041c1594001c11003800079a8001904041d030395000326010b015050340f55404110301030b0942025409900104021402d00745400207041178092540d51071500980d215860355649140b0312410000c924208040c0540494030030b40c403541030030710469060400d40d0300e6450340020800700072204d00140fa44d081006d010b1801c81c28804c0030b082d40510700c002c1810810724071610780d849948160920040004c94108020ba2406240185c07243d044480000c05200d013032018080c00d043c3e965601c60b001e980905802c05000c1d10506040c1c800c0ca07610603050040c071051141204d0800c00590051203020300803850076000d2054610000c0e641400081002d0a15200280c0f4160000d800e0794141c101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 797550764 1250 797549514 797549527
    0xe18010207080f0301261f0207020303040f0e0a0519052706100b07020303040509040f052407050310090b0609031905010507020a050a0f0204140a0608070807120f020103150e010515 79
    0x8001802040c8119440c2440b40003156507c480f90092081000080d010b000108001411400703a02e1020101c800c54290000181e480b00307240c104449084503541111801411031029005090307101d03642c0004110480c4c401d046180c00601500e5904507030038100e40c0d108404205d000315010f11403c0042180009441c2808080d600094607809140505401100c01400140620146902e902c00d6070340c200085c0c5420003503404a09055000a000800503131002d007021410191080341200d20403419a02d0604249043c0144030001d460074050656008105211b1460030b542c0c103200c41515240d4130300121483d0b8141e403801c83c0c01d441c0020319940564100040384004a24041016000d843d4080c010440b00c0095200040c01480c2005520341020991000c01101c81c003281d1121f03090b250b500d01105c0500da910211180d8496440c01000390207811800d102002401300c3d080030034442d1050602060101d992990f5140748400e9500214000d640b5500401c43c40c1408024101029101c924440c40c124 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 797552014 1250 797550764 797550839
    0x150117030705060f1308030114010315083d050624041a070b1501020f01050c09120316050715020c0906130b04052409010e18010207080f0301 62
    0x1100a2141c131918005100141c0826a807102c1500c003030f64010304154403961102c03e0039044a00c0303407800c0c40c08680303803010038011800041084011502034500038140700564100210600d40e418a0038181c408040c00110b0400500f00410075845420f5000015140340000400c10400700031051389440412000030103c503040c000084805541541c03480405510b010007007000c59202e00080035010506400600c58441b80719410ba1301b050400343c0c215001c01321070080c000d0880f2425a141c44030420304124154081c10160745040c0010110415203080c06107000480c501c62a01c0303c0112950f820041091044085000b04105656001d00c010314081401801044941c0b02c00303400b1511584c6ca040c00403481100c0c580014030b5007080540207114030f003400c6e0140d0b010703141e49001d0b4007552004517070000301c1814090354040c1200c3c0000d080c2c2070140c5800c84200c1e4060390014080c1c03641d5408005800101d0b0f00c2c10024400310032000e41065803980741c4080c40c07484050070802e0000000010803007003450f2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 797553264 1250 797552014 797552023
    0x10e010b1503150121060f06030e0d0509101205040c0302010f0801152114060a0603180206031b03011e0603090f021c0c0806010504050f09070608040201050c150117030705 75
    0x155017802c285200020740e14112003c00200b80300643c6503414194040380401c02c0f03040060032620143c50500503008404e40641d00c3c0c0203421203440003da41803108142ca45001d8440c0058208141442c00c01d03815129003400540e00c08840558840046920400855920060400303a0414a140c5a403955040c211305541083c50809a142041000c207080c0e40030400e840b0002240a04444080090345442c92400c614618111501441000000d4002520074082e000b0640d840d003100d6601003c4440030b60800c00503801c05807554a8a55000c0940b0314428400b100560192244050f9040800414100c2c80241401500010201400c150b107480010342e421422001e415030454654260300c40b501e00310a40109144405440302e6492000021805d0300850124182d0380300382c5050145598140500981480035101184a60301002c0100941482403a009070020304c149000351400d40c540c00514500103c0c10001c0040031020380040003030821011030316150b6006407016500340280e503194503854 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 797554514 1250 797553264 797553301
    0x204032901030b07050d0216170c0705061b0604081914031b091306030605060301091a0a14040b060a080d02030708090a0f061701050607020d080912010e010b1503 71
    0x20b024040007160f1413038024000da07000010914002c64840c0710b5003034a292481000013095410319014012640c50007032423404c4a14104040c0c0c006c0c0045807910050041d03d501c030703000740700715241166444400c800044c89107500440c0100080d64079101c800004176001e8000c54041014007404007103480011070307a2400e49a00c200311a0f40c01c0e00180c8103141c074000511689081030350002500700d910000180740d030302c1241983c0c001c0310308106a9441409150894140880142a81000342000c00e655040d00c42c00d980d0011a0b0000426452000070640b011702c07030152012075408002c0e608129043c01c00200c19401041c840c0010401c0f276100500103900ca00c80c010000d0010303071340010780c06078036201c07a403c3d580142503041000a0030390744d03017400402c00e034074a1a81e0384507444044000505445d007030050310380e42034004000c404180070704e5854804a5100b007010b29080400c41d001401c0300302e020701c101c861a841800001c1a00541401000066018100c040b440c03480d081c0b0034049502c0254421004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 797555764 1250 797554514 797554523
    0x50d0605061810030b042c01021201030f060e1219090302060f0a0e0901150f0e100c0524070306060804080306090403090f08071403030c060c0912060109020403290103 73
    0x410f0a140700084024001c50401e13281c00c1814141d420710300d18440400168414204d040001001c544a05240c1c240d2103401403035200d880d4000010b0001c540302950b610b1203944201d50010703406c030300100801c0c00c00105114030b0ba4504c5003c03034260400e80e04034034408800c0802d49841141c41e400d682c00a04903000d0b0002801848d040403480c00101c0c0c1c082c286001100b10000c0c1200c169603981c81400200040340707104080050f0301102c074100e03400c1c002c1070311181400c8000d0840f0900340c2407880890b40c228900e80103569500c10440c0322030142080c9040018420018806203405161103200502a07079242e0b4400000c0041400400001c6084402980c3d00b00f08110340c00602a251070a0803502d20391035802000c0c0a101050000840381c1c00003a0110813902c8240c00e8501c818003500425440340256041000190450030004802d01c81ca0700013002101001003400042414404e0902d2408400f6006001040e500003400c2c0144072201d5201020440980300c2c0f115200d443c1c103488c2071083c0b01840001c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 797557014 1250 797555764 797555779
    0x2100b06070c0e2a0307091a0406050703030605060a033c02072108041703040b0417040f0b0409060b0c1c26340c05070e07050d06050618 60
    0x1885101d485030000d80061038008000000884c24680c004958026640880401e44a810001386001c48110104100d6040545107007024507102007642d5035408400c044007010f60b104008201940c80c00c01600e0201035035680052140815001466651606c0c00000d030924100c03d84050242d50342120340d0200070302c60402607296052403800200325900d40c000c100c1a20303a0407050f07120305c03580720030024070550144400c141036920b4892010b08a00c82500d020300b03900029000240811a0964400d901009401141c0c1c03400d903440c8000c03c1c91940f1604080c0b400c4c100000e08118800311400344001a2803408442c03841c0c2140c0403140c40e51000035285078403005200c04e12060340306010304820546980c00d200c20919050b41c40782007284002d0f0464140b80c00082d41000b05c0b090410100741c8a1030b41d015036550001c0e5004482c0c1c00d4400820204049807a48941c900c003041d20402040c1c241d009801585036603480c1c054071040001603070216000280240750900141c0342d80303800000400d665800c00d40c1e01c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 797558264 1250 797557014 797557021
    0xa02191202061806030712060b0906030402042a09090e010501050f01080c070804030c03060f1b0c0c0308040311130b060d18020904121805030d26010602100b06070c0e 73
    0x824150710f008034642d440724010041091039500906038110b01c0001c4003013007004603107074210b004960103040e00140d04200248001001030a03c2e9004c000c42005c80600a8511100740c040e00d1101510500c00e2000581d00b00410010707075a070350140042030704c100b4000380302540c14030b8007048600b07108286050410000382c3c007241880c01920119a40d29030011a05d940c0d880d103d080c110940c4580c1d210480701589800c1040c0100043c0340b16403010fa034030001150000c546102001c807603c01503050b040d540c010320208004001045800140002c5126050381c0d0066140031040103074144003204010811410102180f0f03183d510f09003101d41100c040c1000140030340f00c0c460040204003c00030000c0d0817410050600c028070180860b1005101200da840d090021603410b03001c40d01910340c1c0300741501580000064090b203805248480c802d404820440480c0113041180004110001e83c04180983c000d50000d0800c0c001c10b008210850b44140d0350300d0700c2e00c00103562b81c24020000b0321403943c8005420010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 797559514 1250 797558264 797558287
    0x90411040803030709030c1d040b060a0905090601090c020307030f051c1e05060f0603130813170c0a0303051204051c02161d04060e0313080a0219120206 67
    0x2603401804401003140e880b07150a80001c2c003104101d00055581464a50001070315502096039520303500002a1a4412529141d80c2e00300100005008550b100880d01804150120305225152203918010300501155140040250031940780e00543d070119081008000082900000c4445665010749405644e034451001d032074040241103c1c24018181c200031240c0b1400009600072007079940d00035020886602c52804004428084200d81c507000b03103007403000511030421040071081032800340203405c0c50612000d07407078154840c4507009000c0c00980c0f81141031a8050401c004030004c03c00741ca024981608549020b0420b009424800e01400d5951001904105003481210103403180c40d518656140740000e80651102d140c680b0003868250342000c00581c40480c03c4000340c0d401440b44640405441e41c5e02c03068080e00d0210a0308500d0300c81009200d0340729507450450707030080c0101c1024040c0900c040c81000180040500d46928a61310148240b0003107d0790040c040c0c0180e03041761029034400703c0e00075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 797560764 1250 797559514 797559517
    0x2c0c0114131a0315090106020c0f03010917030114040c0c0f03140d140a06060c1b051e091630020d0209030f0f03030a230403030c020f12090411 63
    0xb1102d10200d91150030304160284401840c00fa1030200009580c203402407050006061091080302d0050b40702000c100045c3c10322206901d054440600085282651515011421010301040d40e070143d0300000104100c0030000c19450040008444c1030000c80ca944070001c101c115034810141407800e0003a03410342054090700747e00790315500e01e070100c0e9110441c2d41500d000401c940c100d00800c0c440c074180010000c103600d00c81e13035054429903100c0800303040c02911a49071407048405615454044088042910b595046905008000c021411406c400c10070050049004014105419284618500440c02d0750000516480940f6455056480c074050500021380c0c60a011445070392184005196201e02049400802c2c00b014150100e911605240c641070750346002c1038541100700d4005001203803d11a02e80c000d003060a281034018001480351103422420300000f66000c0f800b00e0b68a11424120940501104e01c0070083c000c060301a1481d007043c100c400e446101d924901c210350354034a210701c9113141070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 797562014 1250 797560764 797560769
    0x6030603020904230f010204151e0f051e03011503090b01150215181203010b0d0506040222030b160c080702030f150406050c0a05090409020307092c0c011413 69
    0xc41d82400081d81a050003588907010340030b100e800c0406010527070f0f4003031020404900c0d2281040c2000d13440b20001203961104200e03c8004000040001221360302040b61500482503e0320382c0c1681d84d500d00442d9240d145101201803060505024441011801c5c12071100d044452075180341c60052481603049013010072100f81d25035040b150f4814043c00040901544e5001102281252603a4106014011f181c0c0000d11510303c1c54003041180140c90078054105a4110901500240c10138800001700301002081c0b641020080004800400c1405002c1c44e5694101602c202000d480e030200c3c00d8014015015080045e201000020321101151020008540050303102c41c2542c0681640034081c6c0c003030503010b880c140c030514100004105505d141000301c2f0104d0105807141440c100ca22014007018242940090b80c5c10f0054000c0011400554040c0c41840f44404107031a240c031084500c8241c51040a601d903002e0381c2d10280521146981010100103003681c41f00c1429101d090012200aa110894 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 797563264 1250 797562014 797562083
    0xa0303121a03300d0b0324130c0315050f01050f0604030314070f030807020609030a080f04060608061305070902090901030b130c06050a1d0603160203040e01080c030706030603020904 80
    0x9000708150f810f99000d6003038080f0442c243c50702147c1d040b040102e140800c01c1900a00145c00c4045112071280000c0f0f080c180f0301c0f031034514400c6596602c0704a83e81070601d0340001a1600c5000b082103542840d02c50754054401112110303024507040f4082405409036020040a02c0310140c020b101c81400e850942e030045038843d000036440f1000d403500609925066030400302501c610004200c110801005940440e48030366614401c940c1c810000c03042c0808041c000383ca41d46c0d556407000c01d03900d0741403001900c16070300d081ca03090040c5010314107103103003070869803103c180c1c24814843c485144d6116a50f0701d0440303400c001c0c40d400c507031070304e440c0e5202000f0351000c014581020600700140140d0040064508000c0c562550540c1110b400703040c0e03028141d10720101d94061310800004019406500141c0f0441400384100e03802c00c0d0702d03002005060402038001c2200c03503101000408030351a0030007900000c1c1a40d4942400380da455a0b010a0400310050300c01803070201461a481c41480107030a0076404d20302c48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 797564514 1250 797563264 797563267
    0xc03020f0a0c03080a06031e1b030b160804231204140a151205100f030b0108010e0d020d05280804140a020904200a0303121a0330 57
    0x12140c05032103a042982d0440c040ba050000244080b9041d229080880e500b1985c12031700944800e07440030000c20a920202c8a80e2100540d8110300848040140c000e5031003500c203001ca50401549505e40c60880d505588100316040c010807000a100b00702086018243e01c1c510f41103464103c0113141880032500c6c0d0b00c50968008580090000a1000541444801503e543e2101c1e03031a640040100c5820026030004200d01d00300c103050400c640d0b404a68040004009400f1907a12150820340d951141c0d80141d40e03504480c001801218401c1c071455100c48170100080140c420646400394a800c1c0804903071080c0040401d903a8400001c40c85643c03450381460302e070b510b0300054007403024103a058203840607140000d40c2804c5241c0c042c4005174802d20f05800905005050780e5070b13602c1e6400c0e1203280180400900c02400d54500d652242c00d50740c3c002d540720b502c0311050310154250000848d10424554200048207003c62941d035200407403200e0540c0b48801e5028405045031406198000040d200c02e07039030000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 797565764 1250 797564514 797564527
    0x3120c050f070c0e07050423041808041701090c0317070b070c050d030b0d0b0402030114160314060604150e1003020408070911030f130515041e0c090c03020f 69
    0x64540500680b80c01d00313094226034032141001c60b2a4001c43c01002500700304030071001e114403011804280003100c02000410210704050300400c040080d010119400c05010400303201c01040c003000c012640030040002c020010380c44d00c5403180e1070140d00c0090415208019801e080b40201002c07a10700c2504205081c6440c104000c2c0241460b4000e6410b0300c0720700680d0a406a1035209015106070311400078090199000507840324001e0325405001240d141d035172404800030741e401004040f4414103240c44850501c01c0c40103c040c0c162264074000004030b1180c0800c00c110355403030400b641c080e540c04130880a00b00d600c1c000241e40e42c10340482d4540d40800844101c00e4003546c140c00400507030721010103803000e1030354506082041c0d9450701080c9200c14070920000707128882d40ca11482c1e00c1940540307450805843c0c0c0e2a400c1c07c1c40c4c5100794074441188070380200700900c02c030f800300750f07003041840c80c0240700001e8161118141e1016a000309540e581d00c404d03074000d550344603805a1302030080440d601070b5901d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 797567014 1250 797565764 797565773
    0xc0109022713030819021605071d04080a0804020f030601080304081612121205010b0d11090d0803150325050d0809040506010504090e060601020c0d03120c050f07 71
    0x141c0200110003150300d56000507941a001c0c2103100c0d6402e0340b5032a40a01611020712030b038092507940010300d100e9070b0f09010a81c80307100d01d21210201d06000b10040c080440c02c2c204009500d40221019500c4082c4c3d04040c000003070042c008442c3e6105040c50304c59040d460303903c002030380a1100088280c0c07500c1620004130f103c1e44040f000700100d0b114030003111214020481c400518180e9441840440e150002c0444080740f4200070350340703000500f4644400074642c041000002c4810a801c1116054004290203030040c109128904080800c10b11160030250322400098900410200007070100001201191b440c0c1100c00052180c1000201500d14a09010003004a0301011100130212502c02d0400000c1c0d0f420316154a51419401a03145483c15040300180006001c01500241c1040410040060420307400c0c07050f002d680c2003101c0600601c0c00d00100081c5040d07001703540d107481102850b10260012b50044e0400c5808000550041500c2c2000c080558142c050401e4400c0c03280400201c400030003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 797568264 1250 797567014 797567059
    0x60506270a0e1b0f040e0303011e0501030b061b07120602070b1608011502030912010914190b0415020c030406080106050313030324080f01050a200c010902 68
    0xc91400d00304008504840c20450f5544400440c007211001c00d481d8901c1003400d001c5441c0300906070150020468088282d85a46107034001d83c8640004100c4c49502c07101034401c1e01e84100100b009190600440e544039002035518403400d0b00c09810a641c0751104c0401c0c0a060041000511085541401e14000d40c00c080d0044d600c0460111140707511040010102c400144c3c2ca003083c84940e03070710510aa070070103180e1410030602c2504101580320512080300603a4411004440040b400c0001082c01d02c1170b480d00e40708141c444034807103989402c5800c2e040300707040210061140c0b070303a007008c180c0c8170b6601e030781c10440343c03100c141d00c40ca041340d42c000076203410a502d00200401c12100703a070b51420b0450307980700310842d014002030320950040100380d518034000c0307846900124400541c3d400c020182e0800c081890440c1c0100782e2112100740c11243c01d02d03400c041c0031f116855200c2d501503c14400440d51206105200d500500300307554040d8041480b4006140941c003003080c1c2c0d54050000c4a400300007042d5652203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 797569514 1250 797568264 797568271
    0xc0f07030311040b071e050c06030a0e010c0903020405070e03060c0906040518041e0201020a0602090414090633010f17090a02040605190e07050c0a120201050615030406050627 77
    0x92522a000404000407034505031b1440350080040c140c100d10354010012258405040e001005849003004403040d1028420107048104586450011901d544180801d030740004101c84248040a142c0c109503440124110342d0115500c2c50083d41e400315a0b00258880c000e1b07811441d00400981d41d0307070310b150308003403d1a03003c0c0f800f40303900c1c42198844409509401c0e0940a00900581000b103103100003c0f0070b6001380c040d2440c01400890b00440c01d503042c2c05101011282254150311030800d0282c1c03031181c2d07c0546200905003050b603019280d0030384031000c80090884541c0c1001041288402d1061269403000c880c013010451400c464100011aa65a20a16003090f413055141c0701300001d003860b102c0d602c0c40700c254100f015041040d00d0304450b282c0e2814000c00040c00e1000410060000c0c40c403d2000b6400b20b4030802060200b43c0b4070f030300300a0071540018a428010300aa0a00f034919005101c181c82c0d100c0d81c403100110f1260340f4680031400d408d040c45404d841100300318071040306265008280038031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 797570764 1250 797569514 797569523
    0x3070f080102280909020f1b010f050601030903021e0f0712020109210b04030306080d0503090d090f0b0d1e0b1905060702121e060702060604050c0f07030311040b07 72
    0x5586000c0c0f0300240c3e4980c41c41d00c19008184840c00810414801d50083c06000303500360402803c0c143c0c0f140e000c180e51009010408400d941d245440b100301c039401d206403a00f00c042881c0400c950112030b81c01035030b1541c0d1038040e00289405e044400f004443c1c20070580c20721044440544003c5035445501020704030f11050704a01107078120038049a114286585901241c10f17295030820000f4a40d00d5036821540d0150003a410140c40d840041403041c1d0401c1410b540c444030b030740c400e950781c40c061190074204408a014070040088446042080340c0b203c05d02c4106941100c039006d9603c4084070343d04401070200c0d1400455102010a0b00305da810702c03551141000000030b646100c40c1003a0a00d01c940b0b00302c0070707000b880d40c00381c0140503c8002d030600311a02083da81e07408046502c4003042c5001010502c3c4071702d42101c0540e010108003d803055040c45200e8202030280c1d0180301e40d0402c0404140030303001e03050304281900c03004a07004040c188a900003d000b80b0350112002d1f078a035140c09904400e80c0c000d01d010385 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 797572014 1250 797570764 797570797
    0x3030c06061401082d15032a061809040827062706180102071d130813030b06010e0f1f0507060c020a020909062403070f080102 56
    0x31503915030040c507020114140d40c2c00b10b5a81d80c002031014131030b80517040c6900c00d0307800c00c1020304044030114a4a00542c042101d0708907000c5807100301071901d420203c0a0599114454401c80e611004501c0ba012408080344d001d030b10707140046808244180d92068203940107034481c00344028046000010101d0786880e890713000315074514160b1101d01e41850000d441d0425007c0210f114212a900300c0881415140c403080c4002d8075441d030000c0c01c2904a6104100748004507004d120f00c1d0741e0104044c0d4000e00704404603540368089807464114803103000b0f2048041880700c210740d80c10007400310100c1d1000c83c00015070709141c44d01e034200031007441006c9954601085440040104c1c520b000c80040190000040000c280e0080f0300b00d00002105040e02c5500c2404024440b5000291103801110700d00c1010741d0051641066030b0041003849070000e891407500e07030401c81c184503115182030120b14403c0002d0000000a0344280082032504400360b01c2900b03210b40e003183c0880c1021043d001003c14440d010510b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 797573264 1250 797572014 797572019
    0xf0b100305070e09151f021c092108270303040b07060b360105010c020f040908250b060306100905130f060221060d0b06130603030c0606 60
    0x40d021508141e0b1501c0100d04208500b0f1441e242594030b031640700f108100d0a0700070810140c081007001071034404641c00308917071013000c4680b1343d4100002400d54080301003204026203242000b07004004940185034010b80489800c0316107088881b001044240d0110381030741e4824120600010b08005094200d0015a00181c40b020344d140c000281c6098810356030200c0e10704031075542c529005013051114160400c41c101c4550032200b4009400e840b1242c0030364098481d002c010420044924016009503041c011102d05034000350300d03203514080f00040c054500141c500500d0074030901c140142000500c1b102c10411202810320021800100480d200307410180c0030340c6810003010380b0342030101ca6000320305c041848100032131811a000380303400000c00d504070310311003c0540f5103c1c400e404410054500f59000507003281400204110600010111603000c851414550000340a00701038840207458901001c000c649183d880d0800410201c800c1c000400070b151360707450082c2000324403084c02e80361203140c1030f0700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 797574514 1250 797573264 797573267
    0x1b05010816111501080601063203040c050a120212010b0d030810180b0108090c37030c18020304030206010b07050f060c0d0e0129130f0b10 61
    0xd03001e0020036080380300c0305001480440b1070540112280c07440380f0410052510491054500c40c0c06443c1c840064401c56043c0300c4d018116518030090b5000308880024030124284456440101000c41011026581d48650a1490000c4c9490b080f02ba8011361102002910080d041002d800061090761704245520541c400c241c229141c09040a800948508540000900c0b40e901e49500841e0381013803039105a210304005441000010842c440113603601100c0e9510b41e0400345981e4840700038001011510303881800300e003605821100016180c9010408107880900c2e150405000102c1e60800807074166481c1804c00d15400343d4815443d41680b044040200400d072030003103070300c99500f540040c6190703460030034424440e80c0881005c1c0c03414000c0004038076000e401400720fa4000c4c5002051107444e03540162200003103d5022240c04007903850680d4400015001102c14001c07001580c0d17480d0900c41e0020045583d201464402a0106240404a91803201103500071080180c080d1424003101350040c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 797575764 1250 797574514 797574527
    0x901020f1504020607081207031d064515010e0c04060e01050702060d060608181b03071814010f12120e040c0905090f010f0623071b0501 60
    0x10381e0860701d00c0c44000240076007004070041084501c500c41c0e99180c400e06202110400f1400d0300ca01c1e0000380c4411601075580403142c00c1e2400059004050030603030800303080c440d211691816290610b034003000102201030742100c00e5114180320803460448488407651100380c5403024240e048803401c51315400800c021050780f010601c1102040c244500d0541884825030b02c29400031250f40c100141005924010303200c1402a02d0002e65880c00400c80034200f2078041c20342c610092104e0017901031114007180f0300f1400500811400d0004160780740010210700480d0a04003640c000c0c00182d41c0fa0901541d4841c040e0340243c004c00e0140422602c240d88607003007a0424032003803140da8040030740d4908800204042450301070072941c0c01c1c2800014200707150041000d4400200c0c0070fa002c1213501000300650b00305560b8265000c860f0210180e260743c10030f000b4840d9400180180320800038080c0720450741d0341003042c0200800e00c03540c0c5002e480e0001450030032500d182122048029924005000403d075000e6603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 797577014 1250 797575764 797575783
    0xe0d080f0714040314010902120c0f010315030f0f0210020d030b04020a081f1e0302010e060403030c1e06110a0e0a060807030b0f10051215030715170c0901020f 70
    0x42c0000c0c9403529507182c0d8403444d5869212059255078138800710b0010780d0380308196160580701e100034025010031003080000c0d4030116a2010306040c00e02080544000b1860b0002c01a698888010f00486010341411015002d44c694000d41140d0324101c1c02c160700c0c2e00054021946880e95a0620842105500707000a900840140794045405c91000c0740c06404410401034000110825941c0307000c2e5121110321043c3c00640d841805203890700c0d0709100350750340588003449201c006c1d02c3e0b0700c0c50980785030f60040c8201100e11001d03000d00c80850200369004600400140c1c0705400410900c814020302c00b290032687d21003140c0c0c001281c050001400c4600f8800250403c5407099140e180040d07890079002d038081c0c0400e401c0240c2c4555609040b10155555507071000c0e140300d4036660710742c48030888124460a00d13406080034000d6034070b2499808003540d0010310502501c000709031240c0315406440f02030300c4441905d01a085c0204295080288442c0007101902021000760700300ca41203406815207540340d144c0038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 797578264 1250 797577014 797577047
    0x1802071203292b1208070e0402030c04060825170a090b06150f160c0803040b090f18071107060906020c06220608010503060c03011d0a0e0d080f07 64
    0x1682c0c2c105460303082116030a190f003400020198032041035a11070002d000c014503042d0115034041c0601610560100c501140d2401c261011880d600b8611548001d40c0528440c0c501080408400602c0801004001c0300644911000c001d125601e00040a040c03004070010307054104012000290905145000317500c041d6030040a406401e4982009001449120f10800d0551550400c11210b00d46000c200600c90411011140115900346107010214180b0580c8508015401404184148607401c001c940140130700725840720350b513520030000c6400790b0580b00c090320100304a0410040442d41000764080ca608982c070035210340b5500ca040940b140a400c0c042e41c001640629060300c5032b420b08200600c10213000d0b942004c2d000c55000040f0740d108400d500440d0010320604010411400c0401078282c010200e440760764290360400345100f0b1000b03042850383c0c0703010441c01c0c085030741740c40142e003c0a0056200000d40300c1c2079814880240c581e00003070301c5000c1e50303113500400611114451000c800c0d841000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 797579514 1250 797578264 797578279
    0x40b0a0212040308060109080d0201020409061a04150c0c03050f0d0f091a3703110a03020d0f1112010509010b161401090f03030e0601050109180207120329 68
    0x2035032000c8640c22002017116042c042c00030340100b51440e0800c4441c0b04000c056001580e1070382840c1e583c105644003a40306015000d05001d480100707150340c3c001e8a080d034054a41d9807102e0010140704840d040e0100f0009414004c44610100501902190f01c02211844904403003042d24426000c0f18021058110480000c2d1441740a20440350b00c889003060300b2000780003150506905004080103000303082c40d1000351a200580d04103404d0800c83d05540c0188403401d003001544550140d00e88144611344001081590000728100d8905d41c580c0310100c1e02405079000c0041880101590102c0d0f440000721010340955100005414504030354510b060b070710318415041c10500d040b1071083c1803d20301081210940403a0707a00d20b148000900c9031042160044451503840c0500d800c01408844020004200035000903005016590308030b81d40104950458544000d000a1540900004d0240382001854103007841c2d40e409800380d243c1c00c200100c104c0e945094503074480710282a80c1c401c20707504016070807041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 797580764 1250 797579514 797579521
    0x5030d1e05070609080a03060f0f060816030f060b090f0405010503100b1c15060b090906011404050303070b04020306091903030b0111062802070332040b03040b0a0212 73
    0x401d10140c8a001e01c80c0c00c01160b00b500e56600d00005030003200341d00740000d568040800c030000301e060280006214140d011901c80c3e040180013041100000d000f8420082444800403800744a98014504800151f60400c1741680b1103031180c40680c41510428421100c2000c070040301d1505100302d0b030403a00020010226803040f000e40802911044070002c1c0d008107140a0450104051a890a0b200c2d1040c25041e0b8004001100081100c0464010321b0111406001120f01a102d02410b50341000c0c0c00d08280381003125210106041e80f085400280d09800301055400802400c4d40c032040c02a44202d00340c0d03030541d6a0700d148a0b0b41d41c5407494690402c00140c841240803030300171751240c010f0f044107142c1101c4201510000310301d02002640e250740c10003071008140001140c0c910010708103034402201945803a60984000304034004000e0002040c99001c4418030540228000e41c2606806e0b14400503180c640d81d407982c82c580d400458060b500d14441c10001004240b10340b08656100d8241b18a10503180c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 797582014 1250 797580764 797580767
    0x1021911040917030609100303080601080405012304020a05030109030c080c0319120f050115110c0901030309060201180b0a1e1b1815081306140105030d1e 68
    0x914a80c899800582e00d0b0460800303d00700020700d00070606051905a507a007003407020705c0400c04004043e0000341100410a0000941c44803032903401c80c0c0c0904c0c00b17030b60588444c1015401010382e401d40401c990010444140104001d000d42c522031402129911911543c4506250988140000040010b045143c102001804200107806000041000c880c205000d14140740c00e00c001340c00b1741c0c1c070200d01c02080040da00c40c414018554440d070b014230f041c402545003458401908812140001c248081134103040d070903210800c40c00d20102e000802c100c406503941c3c140900030303031201d00030b410041d400c10b1100684a14480c0f040c0c22034550146034a015031b030381d54403400000c003800c8100300350f4000b80c81b214410f10b8a40303004003044c0340c5442e400c1c251000c0389400c024140014522b005640008015020400264403100300d04807580e203400c0442c0143e641c2042107030803072140718008211916210a03030f152041c0040c00f4138140d03101501110180c18000c0c81c140c883e80d02c0491508640c03120b040c11107403007a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 797583264 1250 797582014 797582033
    0x1508010c170f1b1c09060e0f07060c050f01050f16020102130b070311010c031d0105010815041403071209120c17030708031302010e010f12050c090924010219 69
    0x2c0c80701041c0c040c03c00300141e40f0b05590b910f50391307540c0281030f441c3e0b00c3e42070030300c405031150704034001100000300440c1c0754103c0001c4d1100341c5403041c00305112860400f641840018042c140c3c81038440300080000d0301d0140042c0d0001e40301922180703030103001d54841642041c0144200c40f4400b007040d0700c0c0f0103402d1520300c002c0150b9111400881c100a20749a00703803640c0c00240694040016251008648a22906c1780b055207010b0f05480785400740e04007001080f0082c000b017a54a101540c0e110b400300c250b80c0700c1c20312140d00417402d88284000d110005410301401040341210b022510159101c0310307000c0d0b550407508454420b107031002d0280b4014000c10800410315080421092380803205490a00c0c0d207507110aa210f402c1207443c03c1e080141c1036200d504541c0c0c0140c250441010908100d00c212005200c0142a001a00010b01069654401103034118280b28150785280c03c00070040006882c120084d11540a400d25450042205110b8140307055800890440e1002240c4400304900941644031881c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 797584514 1250 797583264 797583301
    0x30c1812070e06121b041506081506040513050712060501020607200703150e0601030c030b040f020d060e120309032208030a090806010b07080901080a1508010c170f 72
    0x410f01943e025441ca01040c04405401e95003521029017121139441032005440c420b808100b2509210360081c081150418010340c1c1011620420075041c0907210042400e82c420b98202c103901a58841030709603449409d03006180700d1241c55580507a6111040c11090541303045004003400350304000000b0310310070f10404107202c0705002c01c81034a01110062101c141003c0c00c58100b5140c549200b0300174883c0043c02e001c4e4000380201c0c2e0004041ca0362450701d541c0e0880091380401050300803030a0104080c40b214044030070b6296001001004c0c500600d1804000410800c0000c0e0128003500d424901c1024128041e05d1040d05214007a47c43c4c050407035070b03005141c0d907211400c45c1402096103001c2a511020000390904071103544900e42424140f907025443c10605170700c4604007410800540c8001507000050b25001c8500707080180294442482140c040c04030003810710f0b81c0c80741d10b900028010b10150403006950320f0603140c03030b80040c1e4021380f10000c0c4c040c1214400d81000d0b010340807400b12080c40182500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 797585764 1250 797584514 797584519
    0x50103021c0c050a0f05010201111305122404020f030c01050919080f150c030702071406120903030a0b030a05070303140d050108011e1802040b0114030c1812070e06 72
    0xc1961503d000445400307441e00444080110306109012550b02441071034403004038030300e01a0030910702c210104810240390040314040d0301070318040d545946003001103100310044482c09102c8040b0300000c41b840c2c10011503003079208065000481d100d0741130120705010f0703406040c0c1d1108e2a0003800b905024195103d415021080840c0800c00502403200744040c00482c044500902000c540300803007100428400b80403010741c19070400070701c09100c0c0c000500340b0031904000c00c00100703d50f010000411030b0103880f0300b4007080100d0b441046003604001c4029032142422410810035919901706240d40e45001d00001007440e40020428400310380120120140c0c0050f15101e54036204105510406440082c1d0101900340e442d04404580c0498220000b1040c0049500420490081c0c0003004a042c0d40c420020b4000c070ba84050a51180c3d2042080c420245d03002c65803113503030741003044c4560038542c03208002000c00a140d0b410000c103440c06507003035050b0f094483e0040071400e0800b81c91041d02e01c8094145613 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 797587014 1250 797585764 797585783
    0xe0309090c070b0f100302011206090c090812070309051927050f0606030411060c1207061104120b0a0207020a060c020112021905030408070501050112060f050103021c 73
    0x1109999800c01551141c02206401a11040c507803801c2c211920000e8013807010f90f440807040200d2065440741c034004681c0c0903e402021003503400c60f03080044c900c4d60003000f005800c02c0002d40645802000d1802141c4400301107800c1100c03011a501880c2c0a4554001e00003032000c5000c0026190a8100c104040f036610141d001140c0e03200241000007422100e00c1d02c58a052044040c001c034103074480ca0382d101c41c47d402c0380c00312481e10400240941c0310051004085641c855803030165900e50000b5192042201d508403103108807464904440c0303410400382100d68505014107443c9441841068904039007007021b130551012000d42e200500140c0007882d60107010740c00d10003440940d8514118500078000e580700d100e940384540c0001820081440d180c40c0365513004000202c1140a40200c0f00184405ea14055481ea252842c01010303901c6003c0c0040c020f58240300012074020199020258181c6c41410f08100e40440b00ca041e105852092101a50010b007259076907000d10110014161554480d68050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 797588264 1250 797587014 797587027
    0x6071d0f0a08070e090c031c0804050c0a060c060510051f14300403270503060c2d090f0103090b040506060111030c06010b0a0203120f04150e0d030e03 66
    0x110710f4028194403402142c00454244024010244090f00c0e5403d410340c05045072801d105071510f407450305d48a0b80070802c100d2100040c148a41440954640c0070020150100c0070350302c43c001000e151300400140c8940f4a844c0c04900300f2510b16170400111040a004503c1f002c00e2465088041164005258248000540c0352449001108000c02c207415098a490314a240441e91406411248010f908603244210060101190700090280c1180039080d42100350f405052003103401d0400c80381d014a4145c81160203006e0000707183d801a0540c203200250004c0c40079035032040c2086d0307110116100403e085040050003134a06103040c10544200040c103001c2801c1003259211150140c0441d410340745504584203102c11907901a240c0c0590070041d00045042c8400c2c3c0701502d4071244188140e503100e402c00030b5251a0b580c024401d94056505818105d1250315004007082c00c3c0c1181250700703c45100300f0840c2100280c0745031085482101c072040c0103101100582c54280d0040c1000a0340c0210380c030050211 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 797589514 1250 797588264 797588279
    0x40c27060f15020c0f090703060b0309010f14100b09010e220605061c0c020c06040e0105150c1c11010c0e1504060203030a05041505090c0306071d0f0a 66
    0x1694014540d005030400210702e082921528401003001250454001c08601d0b0056616181c10031040390040f11100100d4540310340603802030400d40e1040c11311010100c204805000d065000c2404c0c0b80030480f040c8080c00c8250b0302150304d007800301c401201125032020180314406681024204044044c1002110001001c001400c00404030900041008108042c66a243d450b401044010101524814207240d003004e514107500504c201e90b440c1319960703848841c01c1d0610800007142141300103000d8036070b9103481c5c83c0c10329a90300090042c0b81c06140028402c2038a6140001180e00d00494078010340840b01c4c104044940036682c01c1d05000c01c10145200400701480300703100e040400340e90ba4a60440000950041c402c0d00326010382c00204855044c0000c005041d00401140c4c2d00640111b400601d9a88034900303201c0c10b41e803500c920629a40742000300310561000145902c034280048046816690f0f5401c011038018917038420b10000070308100d6040c0480e080c0f03004050700d022001450303080d00f66141c281 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 797590764 1250 797589514 797589521
    0x1090803010b0a090504020a05090f030109060e07090e030f0d0903200304061d010801060c060e032b06140d03030204170a0201090608070c0f0f0c0806100806040c27 72
    0x207a44210b80016060700d005810081641c02040c09603070035800c0c941c0041c40036000e030040703680c220f002d0442032117070103c0c03a0307021b5009503502c59202c80c0030800140000a0300b80c0e6403000d800380c1c0200c240380a00f03008801c0ea000090f1545000d08034015850455004030401c00740c1100302c421803c1c4580d8402d88039209941251086020410100075503d46107041e80090200c140403144c040441042c01d030b04107007039a0004070507043d50f0880c00c2c070f10410085031400302c1c020300303a10074029018000800d40c2c030180f564030300c3d14a0205900403c1003009040c071454203000c40301144643c05071012010030300205802e0400c040202c080c024100103050682d903240032541c07070f00c4420001d0500c0c0c100085038800c560b0030844000290901e0328140300f00d89000a006000c017280700718003a00240243d20102c3c1044032085228000380e078030407440005290b81e450007664402e030503a01a4088003d1140c0802c0c15840020707a180724a40201312003100e20725003218203400303507162441c1400f003e581c40d000f90149082c0d0301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 797592014 1250 797590764 797590769
    0x80f0904110d06060e090a020c121303020f04050906280204031b060513050405040c090f0506090c0901090b0309210903011508030315040615051e0403080d020a020109080301 76
    0x10034981d54401c12000b5104a070b6040d0810f40900510032440c0d4440d883d00c030b94180e8403824080c40107070b44550f00001d840c41d24500071150f85642e00c00080d02082c41515a2504040368401c0c0c1c3ca110070123810038208000d0f0341c0100d072100701c1544001e00041d5459102c9011080203038850654001d01101100b4442c00d0b40d2007900162034800f104412110380003a9101b194006100b9882d00904040c50320306803080550851040520072030300c420100d014804014807040061445c0b0104010301e50640c015540681030465413640700e05e401c0c0c000241210180000c98504190580d05c807902542420b060601a03000031340050030502c0749007020104203d01c00a407801c45000c1410451b21602c050042509451030291074640b45004003100304040f10340002900d400c803000b800d82031402c1401c90081b400500843d1b014a0882c001c0c040340350301c0190800300800c1c042885891501962806440440c081d01c41da20000b40f46442c1006105480704480c0d01134800d0b03144500c0045144002d40d101c0c01d00540003038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 797593264 1250 797592014 797592041
    0xa12060b0423010c0519050c18070905011b02090c0c07030803011703040f03032d05070302120306151b0d21060608011e15020d022404080f0904 63
    0x109000c1c5040302c40d0002400b800c091034079240001c8142d603040c0e2540000d041314159a2450484907040000c203010f02005400d02500404140e240c00944680c400001c1d134840303010419801d8082819446500d00300c00445000780c400b149414107070701380191110000e20441c200101446000d44050003030008200440c040d0380150344030f5040c00c500e12999030a160700081030f6441000108070a5034900b440400b22601401c0c5500c5450a510620b180114a1342c0501068643c2c1c1c0501081682c11001400302d150095085641302110b40b140340ca0a480142d901c0ca81c0480c41300e1120008581d14401042c5000280c118840b82c5900070110600d0140301045002c08079104c00345c3c4401c101d0551542d45201e52100fa1300748134031407a140c3c0c0501401018047c90ac4012050351207104014640e181000040203c1e452094100141c03040007500e5100c6510044014003030050749aa8020700b1000e4141d5141002c1c420b01c14540304c4d0760f44c20403958011550104024420701c5410000e0b034540c407d003030082104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 797594514 1250 797593264 797593289
    0x6210e03040306020408070905060a090c0c0c06021b0102010504051e03070c0806010603270303020c0304051203031609360c0306050a121a09070e0103030908210a12060b04 75
    0x46c401603a007030080a802081009140604002032951a40341482c1100e5049200040b0050540341c02c8804001c0304030040d2001801d0900068500d600142c1c000100100c116401380c3c020b4504012801c1c4c49040d00d0141050b03028814a80510b4203864214a48070340c0c8904403480d04120381e031400803200181c1e00480c100d8200c00e00400146406000c0c0300e1000c07181a610000120008100101c03006415402604055000c1990460b4810800495025041c0102800c0d0b08000381c00d000d5640c0d0380122551030184601c00108407440303000d51107080c01e07183c004200b240b003902d0601d03990410184a01105a0300326190460a02e401e00300c5c03007002c500d400f1071b5401007821401d050920440c030b250b0b54088585500010b41e080040f544000d103450100c601c014807007145031610042503140c050130350051700c0c034074030282c000108160300802008200e4400009681000b00c0c40580081d9101021160510041081009000131445501408000078003a03400082040d11184400002c0d0002c1e042a450b0710350703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 797595764 1250 797594514 797594519
    0xd03020d02060a060320060f0f0c0c1804080a09030b070c1a061008040c08151005010309030e061b0601090b03120304020d1b030206031302011806210e030403060204 72
    0x20305202003644032076114404e0240528555443c41420031810301042501e1340102659820b035a401c007103d4080180f811419107070854203d040312541d0007072070798050610900d00c1d80c840c54104205110400344005480e04000d9440361165800b6901c10a010720400c04582d401000242e40d4881490041840d90b403840d10000a51230414946101300400d00c009104a00400601e0f80d1920700c002e00c1c591440c6007000464407a80b0704000c214466070840310301c0d40641000e11000700070403081d6500c650740641c5144c410b55695001035044449991000c2c000070900502070640d41010802000e0303040c5003404d00b90381100d000b0b0b00c03c0e0a2074000e0f0401c0302215159103201c1200d04d0701300900e0446162510147e442c508182c0d002444103c94040003d010503170030000c0011581010139854002d5402078400ca5892800100e100c60031040d200d001c90205926118060141d00d031004e40e40140d80c0c4a0b02c8403084c0c010010395011140c04611502c400c20713515081c56051400003403001c1d10045100d400c0243c0ca5a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 797597014 1250 797595764 797595767
    0x906060f06020c011e030908090d0f02011736151023100909091505090c0102150a1d0607020106080319080a020f120601020d020313090c0e0d03020d 65
    0x3c1401800314100710003c10710180c030015511189508000301d0500207003540c010714113120326001c3c40010950000c400c82e9003d003404031207103492003024401d80c5c0d03c0c0e16240b100c6100003850303403081c0c075000950040d20b1030795464011160b40002c0132402d4144e2210844103000541e07071804200d060fa140814400c1d005021100e13042d40b4032040a003072401c2190755151031814050841d4104200410710411782c0500c0c4181c40750040358181d01900c1d80800612610100382802c41d48a0106100185070303c2c603200000d01d5040780810600e5101105078054030031021081d0302c0341c01c1014050080c4503255500d040c410000c0d204020010750820100e005040c10389004070300a801c4500d01e40c429050780d08208040c0711004150f48100300701601d10b081102d150307111050f00e00020300901d120041c10b5200000d0480e060035621041c2e078442c400036404c0b504400c2001400303d840f402500314188081c0300c440014428107245400100e180109460a05101c08012002550110308204141c01607004502180040c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 797598264 1250 797597014 797597023
    0x250c0212010204121e0b090d09090501050913050102040b0a08041506080d0f1206080a0606050301020f0405060903010e01110c0d050f19020106080d1710030803190906060f0602 77
    0x811400d4000c604007403400300404031240c40036030010108030800041c0792402ea6012904c04151780c0000361948503280403800942e548060740b000c0004100c8204001a140850f402002e058440151003442c40d9129480c450040903500300003200c655400b40030109121f0208800780802c1c14480c0c0e1420010308144c18110015241d40d510011258140714060201800000b129100341790180790883d110100e410b421204011102e002c103040500b0081c000038210000207446103058003c46080021565900800d030803440303035003005001312000b800104598a82071014040030003024001140c081600160142144c80048030303e003900e0804108090340b16820022581d021081d81000387c5000314920b00c0042e58095058012418900341040303244440c400e401c00710050035210101c0d44001e50070744001d4805c1c2d8501d60840104c400c0c650014010030000070064044980003640c26283d03884032220403030044a000515040e0686491504001401c90b12a1600402800000c928620f04140000307060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 797599514 1250 797598264 797598289
    0x903080a090b010302010f09080114070201051602120c12040b0310320d12020d02100b0a060305071b0503071e030f0e030a0203010603050c0301060f1508250c02 70
    0x4914054003800090101c02d219030541e602402d101c44c00b0b40b04000211340321511174100e0035055003000a0301d203a1568000c501c81c001d00045d00284003544d180310001032370040780003a40005a00221501d110a61010000e00f09040ca46042d20204101081c0c07102c00c9600c90b0340855a036000010801107502c0c81c070250107001d1701d4080070921b2000791807007071050080048411820000340300e00d80321038035582740030500340702c0350b480703030100c0828444002c002c0e490391070003000d100143c0078446240c000e0340f900d4410054030b404014100e456160510b00c01303c009210090085003488201c030403141c80c2560002c05444010301c01c6004594607241454145813100030700720050b60100c964803101700041d4122854030500001403411342103008100e00003d1601600c440040d415504e4442e002c070034031001082d10b640c4a4000c1e00240300103a903031030681c98014001d115070907000001c402d044000c51b115108141e00690190400c2001e6502c0340054034020300c050440001043c0e0700d0201c0d90840c10404140d80c0d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 797600764 1250 797599514 797599531
    0x306150f06020f2d01050a09060b0f01080c030a0612210305070509090403031b08010e090a02130e03040506121e061c050f0105090604050f070b0d0e0f0f01090308 71
    0x1a21010a89995075040c009444144c40101007102038040001010910140c51003800a0295040c40041e050081c80240c4095038058180f01e01da0580c2e00780000503004070001a07582500c199a00c0301403142d180c1002d0908940107407503000c001102044203100801c2540030304030701c800035110000003103846102c407000c440503d400d1608024207903410100f600c00010b01135941440c41d98aa103001c070300801940072520070400e420f802d92144194070558090594070740c2000c0f0229070301c84001c420795030050700c42c0081d0300c004200403411206400342c010300280344241c81202e05058031100001c0b01500048599403042c841c0c0010410b07046c24511610240d1048004542100c0c140840400c40c107a02e1210056804842c210501040003810014800006a00b070000c01450811002551304c9503425a0140e40038070809101244581001c80c0e0385040303d00504087c0d2030b28401d4a503c2c03018195510220106015a90020010303001c207001a001505003030000080041c01c601d005800c14030017900462 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 797602014 1250 797600764 797600773
    0x9070902071109160909060e01121b060315050901080a02060a03060e0103060203041a04170a0507140a020a0602010506030c0f0105090901090c0f140a05070807050106091a030a02010804030e06040306150f0602 91
    0x70a80000238100e90544040000ba8130146010303080c0b019401c54540104031000c4019800000d50743d60607405101d10103101022071900725a2442040b481100a0141c9107083d0410201180103203044001480c0a01003170501064440e951010062170348005d0380705403102e6800104100402240601403445000000c100c0b580900380f03034070340c11032444090400701c601410000303c0103c5913014500351800a40d0200303502200d44100c07000e581d22039414131000c0b030142c004644081030300381c018080c0c9407007444083c0c020109061003204010249800007030050620074100f103650f000c4d0720380c40001ca0103428007810110f0b040c5200300c001400c02d11540d64500402030b890f20b009480031a1141150344034046450700c00d80b10503075401d0409a91140c00340007442c40d0b02e44440083c0910450f000121040d4243d5118020b6249007402c0c181c43d0460f4180007400151140006000a4062082d205003c000580910f084c40d480b981c07001c1c100d546441081214815048013007003418050700282c0b01902c1e507803000c0c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 797603264 1250 797602014 797602019
    0x402160c08032115040519020c01060e0603070b09060f0c0109110f0319112806080601031407200307030e091803030a0b010c060609140109050907090207110916090906 73
    0x1800e0490741e440c00c0620560301d46c1d010504002486880241c0034072040c01c00c55440705e114034880e000300030a1044507042c001580010384ca514021a50408803118600c2107032070320102404019040d8001402c80700052414004034030b40001c00d102c2c5100d2140b080e0118031001071600100b042000800705114800d51012860044000724404503000d05a0b00c161300c00380e21281000000c0c0d48500c0c5aa203400b107625a24040604400c45c421400110b40003616a82021f480e01401103080c0c41840c40103140d501c00034004541e0700ca105080b400605a50360f00003409419101c1d842a040d035104000136400030b5841b1072800e1462404d00041ca401102c0e00904107800c600c00e02c43c083c2c036800003e080c90803480d40c680b400c032056402644119402c540c010800c1200c01c2d02c64058400401080c1160500a54540004038003940d087c41114010b0843c2c0c00113081c130600e00b43c662000b030341c003480007160b00c100070790000160f644420f0081c50040c01000c034204090f600904004051901da640300321403090400204 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 797604514 1250 797603264 797603281
    0x5011413060b0d0f0308010e01060206060a050904030e1f02010e0d0206071d130c020607020c1e06040914010617041e0203240a1404020901050402160c080321 69
    0x112080d10703072125020030302c00728020009500391241003001c0c1440406079000003c040e03200162505960072022004056600c0b01022030384c54404880040d00441e601e41d0900042ca81480515400351007031034500701c4086c80e84003180207900030307800c54003d9810050030868219020b009a11070401e90b14000c00f000c2e620004021f542d0303400a00400d0034001200a9480300e01d845080400006802401d840c00603085043c6220003031240c1d40c0401b005014000200341c11510210300142448001010741c8824000103200750418541246a59444101080006445404c5008442c0001020140d4002561410702d020306044141201002e890100340100b10001d140070200340c2001c2c001d03212641c04104103201181c0b4114024950a580701d41402c00f4006030002c201103a480703100241c1d000c0c00070030041d2104001001080d90300950081c0308200601170342c101a405081210541030586194142e40e0321a80c20b1109242c001c451541c00005085111081d90b0044140741e000c104a21400c2d032410001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 797605764 1250 797604514 797604541
    0x7060804080d02030603030403061104060f0f02120a1218112d060706090f120c0803010e0a110a020a0605011d060f01020708070b04050a0605040810023004050114 71
    0x804000c090f80130000c1051a10200140c50255a00c40030170407450030300f1658400345802520a010005960989207024a0300c01c4000c01160300140c1c0041c002194641c0051540d60402e14000c1c0c10402001d03020044c0340554082c619031002c0a802030081d8500c20f08000c1d00c60409121058000c4d82803488443c00b0754150340382c48080f0b071260320303006091161440020b111072082c0c550241400c0d0406414070140a90680e00c01004c0348a028072680640442105503010540014068176441c0c052004001c0030691a07030701c2e03502c0000040002400c0012184211064009a80301001688046051030402010b48a001d002d0034554071035120400100303401205241e00105034500401001d900e13a510f59000b04046c6001d010544240e0b115583c69083d10305c0300382c120340b042500c11001c40b500010418001e40c116000d940c3c42d5000341242e201c0302d0362004003a61010100202200c0040901440e030812440e440f0341c00517402042c1072840c101410643c2c2903130001024205606070050074489000040032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 797607014 1250 797605764 797605777
    0xf0a17010b0609180c070c270c0e040e100603080309370c0302040c020109021921170a030203040311010b030706300b01111504030309060b031605030706080408 70
    0x150511115030380c0342c51860090046d40c0004160322108000425005070b0742824800404602000c1c000d00c040c441c2c15032042e5500d0300d80450100310382c1c0b180c8140c40d0034160041c0e40e14143d0401241e00c0c9150340c1c255034044030a80e900a503440d240c080240300d4092000c0c00412401259400452007140460036041c880003280d0550b005022a0300780b402c0d0402c00041901c100842d00180200050340e0820740190203001c04203003c030300c12194002c0c0e140400420b1101c01e0140c0b038504601c202007404013169142c03007800012055078200b9803220581d0314103070300b13100900c80810103590160f281d050900c0c02406480700c034041a03085904103483c011068038006451011205a40341032140d01940c001d039504140000440100c00b009078100c500c40440311a00401a0a0000ea950380390305441d40d516076845100b002c000c240c140d00c550001c0b402107840303504003e0010f40520800504c1c10b50f0a07001a01d0a0114071a20800071507030348040286140c00c3c0440340052040e400c0c108418030f01a0f507039200314862007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 797608264 1250 797607014 797607049
    0x312010e13020108180f1c030617060a090201050c0d1805030f06150d02090907051810061206170a02010201050a1a0402070c0506030118180f030309020f0a17010b0609 73
    0x344005038a5170320030080d0b419501001801d4038007640c0000d8001c0a1010940c48600119080000c001650070303864080200705901030020381080c0d124010380b00f014100c10f40040c2d040043c14001c2c0f0004480070303c01d6003425001038680c4545000072030548a405116644024031030340161003040b40482c1c001c51220340c0200f80009040329404580300013150718000341c0303000c1c0d0080e00c0da40400584d503600080e46015108211f07581c00180400303071480c0b0481c08040302c0ca058007072382c411310800000e03016034201c0c11340400c00c40c008106140c407840340c0307907600140010445044e4054101c520a40d40c082c4121030b04080b62040c2845540080c2040603449010002c003640580d900060200074020200c04842c003800c03000700b8050781da50390341524200782005404000802440e00c0040c1104040c0e400a040500ea0300410409a00c42181c03016002400d10b9142a40c0103084500b2044065461680b40300c05468a054485244800300e0821400c481880241c203016210401400302c007581e814881040d00c0085 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 797609514 1250 797608264 797608291
    0x5030f0403090f03060e061b120c0702130c080f011202010c050a05011b030b010c0c03110a082a040e030f0304060f180303050a0603081603020f0312010e13020108 71
    0xaa250480c0d0b402102d620030b100708846403034088100181d541061a001b49000129021900d90207a102d001d040340b03100c41285190200522320740382c00181155548514408074080c24070300070790045003204890713005500c1050350320030440d00319a03002103c1541008030b540d1000c40640c103084c100110341c810303804040d0500900205403c1001810058411000d91110003400840740b0940c0c1d641c4845c42080030303940801c0c10203060244a5101d0800c2030310b119040600a41c01d1442e5803100b01440c2004072060350000021074001c640c680c0c041201e00030720020400d851101403c1d043c032580c031004910607124401c5013015900840b003403001050f01c0c0750343c00c8400c1d104d58a40784ea00d0240300078901070400c00411420a910240035110303040100d984a8000d403030604c0a03545003161713403044a000340030050520b02c050164841565212442d600d140303200380101c400d0b91a00030303411031450300180700b00c040f6088114018480201c2c90010310345c000f0002019542c030580701b5030002c0d059040080040e4400b214 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 797610764 1250 797609514 797609521
    0x912120f1a061b07080a030f020607090620070b090a09090b01090b1c0506040c06180b0c1f0b123f0d09030813080f090a0b03090115060c0305030f 64
    0xa070740f0302d0b070b41d15440d0003011030380305a994031180c0d6220300703066405502051050551001e040d0000c03483c4c81c880c8030316994226041d400d047d800e6a060041c40303626400010190301105042004111180c05090b0904003240c641c00c2c100c4c1084034170f07900c40d004104030504110840700050000c1c500c541c1376495012011074104000710100f07010800d0252048000c0340c10220040600101050903406127000d18030101c00e45444507026142c9402d44001c45a039110b0f040c0d410485480403802622161000c041603a041c00d0501c5210404104500e4010b5000c03a80c4402d803040900d06000f14075281d020340c801808039201800401201c0f84064080d01c80c08682c0c40314100303040c03025907144141d150022645a80c4030b5014080c88401080b01850481c0031805101c0450101490b10b100a0085a84a03100c01d2038000313014020050354016203c4160418540d034408504400400c003d075118084510000560032142100140e142c20b49600c0f0710203110200d9590000701c0e52040031607500807440c0c0180000c40c2c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 797612014 1250 797610764 797610787
    0x40204020705060c030f0705040320011806021f0b0d0f020a0b0d02030402040c30020f0a0c060609020a090306090c3210020303011502010912120f1a06 66
    0x11441c01e004041e03004210800c411039182c0e8020394055a00c0081901856580300d40c01c2e0381e24403d0740406480540c017003124264250301341203045010138041c54a01e0300c0405400043d04000300c01d40000000d0381201d1800008211501e40d00c98101d0f000f41000d100c4a5201070204403002d000c41000303015a00d4000c440c00a644403001090300520124650700d036100d800c100000025001541d0417841281840cad034035130300c1034410042c01d080390141c042d07840030000311070210a8040100c1c154801009409128200b070380b4002c1e801030102e46d21103031200142105203180240032589a40c000d02b003041d06c188082e00c0265400700e0118103a0b0f84c0410002030161b01070504003614251640282074004444909440d0b0594110b41603422111810042c0c01c5c8800c405d0402c41c00b00c0010350b107000168401d2004010206030b501030000300340405d000010b440075481c0c40341002e0144840d07100d03001c1003943d422001c03106020701c5a0f07040c40d00784100c204a0068000c0c1110710042e0091041403044a001c40c0c21071404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 797613264 1250 797612014 797612017
    0x3030a0e0603180a1101111b1c0f0803010e1e04020609030f0604030905030d0813030f090b07030f0e10021b1302040f030507150e040921080109060902160b04020402 72
    0x607000102150134104c90342c80e0007060115030400d2540003d2001c901021001c1c1c1c002007e80ca058991404c120042c1c0c0480d040c490001d60442088114040a40e14000031510002c1c540d00d01030300680311140d1300e60404040815810010b4141c50000091a0405104645080003150469812107285a0700d41130540000e1901c2640e20351095036000f404180000c150300042d18000f01c40098051b00c0030000b00e58004e6845040c11101e1490045001400a00203031140c1155000001ca03800d0103405551901d00071b10660f04442e9080b000300340240b02c000e20b0750740c10040241c03100c8000c9881540108543c0002911240540c10f1003281200b00c1411002568030240c02402003110840215229580c0d96800468424640300c1540c013401119804038400e9480404c220740540c1a40b1403070410180001804001c000701041660901080d510000305803008507000c1020742c00daa5180e0301a54100342e041c00403281c3c1a409452402e204110765003030729862400d00210b41c1d80010181920765102d00108010307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 797614514 1250 797613264 797613301
    0x1205030a09080315030c01020102040501091a1908070315030203100c050c0a0501060306060905010e160228030201050f0910020f0d06060903060c03142208031302090603030a0e0603 79
    0xb140404001c001c0c180118000c1078030140022002c90f6084800c6500580c200d01c661f00803940000c4035800144450380c0d01549000719072889080e03507840d0462000b1203040e843c448072001c10000d1440814010b03a5a49801013407100310b01a000c03400b00038a10341c00aa620300d20509400803040d25488001d040300e010b90140c0c1c54492440060358820015417a210b030003852079001c2190400d10f0201d0100e52282e41d44107943c1a03a01305086607030300d030f12074110604140307440742c2403802184100784550400000030503481070710007240502c1d210303420003900e4041d081d40d00040c000380c0c1e0040d040040004120340010101c000a0481c40c00594030b003e8402d110ba901e01c9611030381d503010b5051010020f001a4010175444c203d81c0038050811101c3c1e001d540407008c0d24200d803650200e80074254041600c101c510382d00311003084004104046039a515549d8440c1d907420031160510005040c2d0708510940c02c1130030b149603221508901461900b25020310140002c4500c801450042c040840002c0044a81c080b036800c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 797615764 1250 797614514 797614523
    0x60506030a09140d050904110301270b0d062f0316170903030403020d0503010b040504050a020d05040c060f0c051902032128140a030612050a02090c071205030a09 71
    0x441d0100c04c00080c001d6400f54a61900941c5031421a031110408841602d0580d030303010440101490a02c10400c88403a2800810a841581d442c000d20141d5125600012028450880032802c04884848804540750416440c5800854106000da02c0c4c4e8805003107e51101400040c2c4051f14a0707018100d58403200782048040e41c2120b04144a1300100000207148980c1c407a13801ca55448004031011a0385001c20320440c800704c2c00901c0144004d11741500420341c04581c45d0001800c1402444109055400507181907508003540c820074401c5a900003d0b1004a00301410b00007648101943c2e1182c0d15007503000c110200e071400b04c280c0011540c080c030003c04800145001c0e00c55184102c64080c1907580103059114600e440c50b107182c00940540d14242c0c1101d003940c0c9508840c111480c290b0065680070700150300405035288408503507818160044042c550181000340070814161040c0440104040d0514150910130311003400050561218500c07402100e02c4c1141d100d407110071103880505040e0034000c0c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 797617014 1250 797615764 797615773
    0x13090509010f0f0e01061d04121224061805100c0b04060501080c0a0608070e032a041d070b0a023306040c2c030a0803010315060506030a0914 62
    0x201d5043d92034111000b100b0814008120850b6184500490180030803000d540030740985002074045140c50140c100b8a61003410507410700203802540c441198101d0105808000c3e281440e400d02c0344402e8101405042e4a04003540030910f045c100102004e020702c1118415a9202e0401c040c0d24072540102c0c080561042288040f410b00d440d00340040c0009000d1800184140356007068945442c8803010b04071480c64a52002ca900e408900300e54122540c0c1c041070301845003400c10000c4001c0d50840030700c3d0140001d080708280f0740c404100420340c0c40f00c2c83c07402ca050341c0c1821101d03024a40490b6603801c652000e0142d40c1c0d141951070090f81080824126040c6e050b01680b4090300281e501c2600310404044e15941100950311030080100301c4000384504d400003a00d01c1c0328162006d034005186049150b403044407001103001180017914200c100c036011102e85201000404c10050440b001c1c0c0e4180c202010248055400c0c00f020886500008020406454a45017083d0501c00e1000c586500d45580c1d200b81d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 797618264 1250 797617014 797617031
    0x51003151413060b04022a011119020c0303030105030c010503091609020d051806061c0f080a080907030f0b070e0a06021c050309070b030612060123030313090509010f 73
    0xb5100c40c508514261043c0d0f0520708890500d00d41803084405107407110760b0b510a813400c1c2c004003109079040f88040c01000c0d9656141e841500c00d0500c007900d184031b400b0443d00c01e0b081c428030000b410301130022100c0d4004e41c410300c0103015903500030502c40100304080c038040d85ca03030b81c40c0d0780f0591805130045080c00495825100206101c1e142d50020700300340c0a00d450500c215114901101e6541c00003440c1071100360405000724045160020300c0b445040404002c44644540070303101c0c0044c107400c03007604a131000c0c80041c50120161300052025032000100014101030344c59516500b918051007800207101c0300c4604001001c807030043c030f10409807400c00703020b032003002d41c440d03101a658894003820b1000d0b01584071810403e1031310400491303104038610005064028139202d03100d42160400350009510140310b16001200103010062180245407080c42c01800841d40805121a44121040103000b50802c101c090007c91007403041c2030843e0000d550014041e65420000c60051241d40f100940c0b2a0600f4800c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 797619514 1250 797618264 797618281
    0x20703030c1e1e0e0621090f030703031d15010603050c040302152a0a0312061511120a02061f03050a0f0203070906180f0510031514 58
    0x1e0104002542c035060410030490034100614101520b00d4400150f0032410400420f19400c501c10b840d0940d410f00342c0c0e24050241c0090f101d600300c841144010f04001c107000146000e815107254001d2441c0f00a03002101413641000d4580c0b040f01c4003d410700d40ca9804042d402160301e0040002c500d5490306882d001e0802c281c4140720403c00f841010006420a004680c0145018086a044075401030402560219401811090b608144604005c0021005c40d40c200d810b20b070034140c0e80f600000320280c0344401540ca4040d08003040700d42009003062a2403010711070404012419181070409007050b215982e803183c006407070081c02082d880c0011102003a80b621050f00010044d024030602646602070070340300421804520f80e5031102410702e60010040501140c100b500c80ba00150000c0c06a503420394468503c035054503600e0b404514201394620b142c00c00c0b400d136846010341c0170f01664002d0240b4107140d40c16010181303185c0009031020b0180f6802050880301079024180070607444d0740405951604868 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 797620764 1250 797619514 797619521
    0x41a040c0e01180f1107031817060f01060e0117060310020c030a020f2410080703032c011e02010f051006090603050603030403140c0a0801020310141c080d02070303 72
    0x41480f145400c0c4481c11a00150500031004145420308140c4c0c2024040d0720110340210100a484042c0c19003d04041248030320000400d00601441c0000c003045c0c2000d49175000042030581c4242d040200803122049640c0e40040d4000031008160580c0540f074441000080c200106583c00c84107e510001d0b90880121010000d00a006040e07000d90301c4181c480401c02d510f0f90340100002c0d20203000209aa182c5071010003000307801184005500c0c01c10354966000c28505203003a0001e40c0890101c0116140d4100200214806c05003804d04c2b642d40c0c082900c0029000701280b0240035104084c031000c58182e94405d510504001d08036a0045c401400e100a481818040794040c030000a66100008201580603002d1a40525000b500651800d403031500c5842c1c3c1c01c40d030036405007410b0168029030801942c400c3c3d4400080c006410005981c0c3c00d080084699030320700ca61000807900c1440442c80c24035a00c010340ea449083c481002c042450355585070100e4076100306100c50700301034800b0607080f081c50351560 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 797622014 1250 797620764 797620799
    0x30a050106230306041209152a0b060609040b0603010e010812030c040b070804090507080f1305100b030a020a0f030215040e1803310509041a040c0e01 66
    0x29442150050840301d000c000c4182c42c2046601640f10700c2c080345c0001c118101e4290082614604443c500d51030380ca02a4641180304a105d0000b2008034240108001c40300310038416a141181406400506944040030340d50018030003407051320081410801611190040c0340360082c01058685d60b2341e120260481d5422084c064680c80d8031400743d494800032040001c5a00641c920420141070600c0c0c2030b0441515448440c0031204040103000018075440303e8001c640c0500c01039203a0340341c545451410360381c43c5c1600500c24024400100d2880010070804035180035000d11402c1c2c040788171a081000b003480c08201481c029004102c1d10400240c1090015075042a80d00c00c40784060016602d1840c03c0350b82c061070045100072030700c2c44042143c45181030b90056290300340c030003a241880c202c0d0118007002c90340d40d814403ca101c08000705580341304c01340f805040500303412038030b114050501380c407071521400c00000340e02403500100303000c107040c041f401d100c00005145a1079800e14668640c001c41000d41c0540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 797623264 1250 797622014 797622029
    0xa020907091706190c0c1e1a0603160b0f0d02130803030403080a09020f0112060801020c010b0a0b0f0f130302132a0e042304051507170c18030a050106 66
    0x801c01c810721341c1118002c00c080250300f961001c10a1030191208003071540000303040c84840b5042c002e00c1c1c3c005000141d132428000210308542c092444c040c020305040c4031a0a05d0200c02d005000d20500c082840c0c00141d6820701c0d04030390340c903858500010703450000b445140d5070910088a180c02c0018180c800000031480380b84207a80c0d40c6020385940242d14107481c4420402503001c0405000d200055100d49187e42c20356051207070100f40c0d2660b840722942241d11082d50030241d84d4450710071002600302101400010007a501c0c081d494440284505803480c003c4041ea181c0b1210001100c0c5014142e20035400040e5800500b00c0d4130b0b6038100d55140c0010400d2040d503011a1904010150b00c0d403a07100582c82e01c070141d0341ca465010060000030070008117441812147c1041000c8080b146003065080b0251140f0311840090080940304540c150100c01c00400000410441003d82400961001e20803604510000c048a842d0f4030041c80445000002904139070b01885031034006401e011054000350115580d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 797624514 1250 797623264 797623291
    0x60e061e0c04050114210114010203040b04051c060c0e040f290103020d0501031101110f070b090f041e0501050a0303021f06050a080f0d0807020a020907091706 70
    0x6420100054000c880c0007541a505200400c140d50041c0c84880b200003040312428904165804c1442c82082058446a900c42d41c000040c0722495000120b001e00c00000d000035170070145000c81d50342d01c620607402407600417401c045101000d0b070000404842010740c0001e00380801e440306000240701003189061240f0503070a2a0a28244c182e06100b4115141d21100c1c06070302c4400142066808050b84c14802d030f0405d5400c11801c8003d40c0e4078450140039520410441031002d48100004140e0412030700c2c60b41640d005039584a0b00081c000840404480c41d00b85070750f031201079841c0003420984405654a03001800c004204041803481c800710240150580c0782040166216018400c2041340703404000c0c0980d10084020310791101000d11461001500c0f04046040c0791a1804550002115481000143d01002c0b16100b03800c0280aa081c2074040380c5821045031a0610700203607034403500c8e00b01900a01004001c5403510388144005005000e60602400c404103140030916966030040341c1320001c2c2c0a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 797625764 1250 797624514 797624551
    0xa02030c06060a08030a030b1309080d050601050c151e180d02061e25080403020d03090314030702010e01060f140306010e0117100c05070327140409060e06 68
    0x5194843c901610306000c010f41c100403058034164000d010003074140d85e00c07140291500c1c80d0601103000780c00032140705003180307601c0d041013801c1103054540c00741580c5d042c00424862003081b140001041e5082c52101e502031450342e04c035402030700b2107851202a502075030000d141c10000d50340507290702c410750b080c00c100c00c480c915054085c0483c2c4418041c4e416080508400b901005080c1420000a4000c0500403480c60740d00041d49150840d0004840740e0000300b0800d50801c000e0640500444c0301d4510542802d010700c808035a0b009120000707031510301e40d0110011020550441c402d61103a40c400c410b00008220841d12007002c03040e540301d14441c0456080d2041c3e40d9040c0c506000ca0917030b040300c4200846001c01c3c0d007080e001c0e0010443e070b05d00c0c0c200305100b040001c10008100d80142211014141c070303080c2c2c0e14221801c0c0100f01d80c0c40d0854586591b80022000d111003410051508125140202c0000c0805000360000c0c010f04004280544081c1c188260f14881c2400801c1c500d02484010045170080748 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 797627014 1250 797625764 797625769
    0x313061514010813110d02011b05330118090203010501031113060510050715020708040f05120a26030406050109140405030f130302120f0c0102030c07090c0c080a02030c0606 76
    0x34503030100203005c1100d0600c5e20f096800d0000d01d064040e4030505100b241258a20842400501240f5054070240e02c2008050080140d0240784001103000c0032241c4081c1c1c1034a014041e60340018402d00f55603102507046041001665400b04404940c001c001340700c1e030b513506d040140e85002c0e00e0034111721034005a140c0d0302c160074544c82000201c4401400c5464481c005003000d50b1541c00c003060580386076190581071000c1202c2e0748000c000c084e00c10f01c4540e07219800d040c46850492410340005010342d8401680102c100800620140c1490b40f040300d42c1c40f070740d8031600f040f00f401c1964121401b10700c501005120401070300d60041410703284090000c00114420b04803c02c04180280d030040c0c007039001001340c08030304820b68006205c03102040c143e6003080c5d0340d13a50120783c55081c0104e8022054004800c1d481c039912042c0442001c4000910045040ca00c000382c50584a01f01c0e48500d8400c0390f0b030341804022a9001c1c9080080c1e20303402181712a01d8035050200a500c90b482800c2501050140310300060691 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 797628264 1250 797627014 797627041
    0x180b0109150321110d020609070512101a040603080316091203080408091203070209061e0f1201020a02030307020c1f05090f1302040e010b03060603130615140108 71
    0x242c0d003005509440c0d25031440011080000804100d0800200d1081030324001c4c81044092002400c82e4005c1606140101c015400c0ca0fa00d44c205c01e2103211800300c2d84c0c8803420000f5102c5101da0f0f841c0c000103041006411401c000c0c2004014070364103d0309041000040c008024013451203615010002c00d44404d6500e02111031140314040d0019190fa1041401c000c20711400702141c1c080e100c0d8220390700c0e045250000400d0b0400c520801d1400f58000940c0e541141131104006420003c1954455540303116468180c500800b030030b50941c00b0b131032819605601070782d0340e0680e040e41d41c030700c80001c542c0c4224841c8020b480b988220717040405031240c04030b00d1100f0700300000001901c20301510070405124001400300c8080d40040f005592190301010000d285a440d032101c04e8000040340e00041c0c0d0b4610b0045030400803407051380030780201c0e5001d1041201c1038503804100ea6001074640030386500341c455840c01a0050070040554000d0741e81000d008118801640044285580c090300c91085076500d188011011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 797629514 1250 797628264 797628269
    0xf28091407020703140102092e031e0b030a0c061106070e010c0303051807090f06060c02060d0b0105070b0a0203180c010c02090709080102130504050c0408071404180b010915 76
    0x6a020b5501000170420050354040428040790016140c4000b003000182c800d4105048075403c4100164080344c21900001d01d030540100504050160b001040000c03c00b03000fa41010804143e02c42c4c490100d642d90a215a4001c2940004000340d599200c3e80e00808100300348208140324401c002c08038500b00d020f20341249803440165620751141541e580c0c210003404000e40b264500055030303441148015424001c030005403180d4a40080c9402c6402200c0b025105540d00010074048000080c1c405603c07414101d03081007000c04c002290041841d401203e9038030451310007038410708580051040444580e001540982c007401c51525426242840054071500c4403550113012a100d65544401030400a80c92540300080d410300c0c15505580c2c0c0b2074076080e640080c070301d030081d01c101040500141c0b07098400c50750411100d60010b801c06003420001075681010380100c1e0000344048102902a036a19000800d000c0b001c08800b01c440d007003502d40309030306c00c100380a0b8506250500c00d14084011103079141004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 797630764 1250 797629514 797629517
    0x111030408040b071e0318091a1207050d030e010f090b07020f040b0418020a1d0a050a1503050309030607140f0702030109021815030d08060f28091407 66
    0x94146000d550b0f14441e485183c08880350f40403d056001c3c41c4000a501d403035014081d84442e401d40b814a240da000100aa41242c0451482c2240d1649a0070800001d07448030801542e101560514940940c5e2414010b41d000c19840381030107946008055018075040c1c200c00f070a07200c4034000c0c003031150103650100d4036002c0e0740c03014036080c0f20b11070162138030701c80e0072480450103880000c500d60f60f5400700b000e455841100c4064100f40740a440e0450400c45c000720010000d40da4102c07805014420f95200008001d4850a00b0545640120b40d0031030403680b12200c04400c1d54011072403d50f9a181c20303034036500002c054922a001c5c100000709014001d0034640b03d0702c3c3d0f030003038443e1030700c0c1021252515a810401d800e9130113640c0c0f01480c5005840d0030040d205580c01c9000603e000313140141e01c041141500301c000c1c50198119040f03208076250010314071380e00038030211483c450001e510b8000c40e8000700e80e10002003a900000701d915225101d01f0050a090703031410714060101141d0111550b9071850203544200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 797632014 1250 797630764 797630767
    0x2070618181a030303130209060a06050f0304050c0307030f03080604060f121a01080102030f07020a050a020d0206070b040303060512010b0d080306060c060a0b0f030f120a090f09020c0111030408 85
    0x352001071540c48048075400d0364a03800c8400500402091864104842c03d0743c0c1c20005030360765030641c50034001460b48254111903a2204908001006017240910396480e003900300c0100200b010400103001c2e9003030401002e0203c80b15282d4904181d0f10010540340305a01103000ca20104425003041d0291500365141c00d041035034000d24007072400008511800702500c0598400d0101c101c80445104018003c060000001d03071642403040c1440784d41c42e0064010000e40d4000b00070b40000a2012603c807441c01e40441d480c00002e403040c00410801e10501000519003101c51040004040e05544000c041e1242900d04540c207940c03031210300e42280c42245401d580540324809000001c0e0101d0029640810060110b90802c0340003000c103403800106540c002c1c0728603100c200403000c5080c07080403410080b00c1140201032075110143e20035114540400294100d02000490400c414012031960006010783c24170311490030790303d2210070001c0d0010b509021455080c56200e004c003400080c00d5034000c035049201d06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 797633264 1250 797632014 797632049
    0x9030e01050c030903011508280611070506040c030b01080c131107080d0c0e06031608070201110d0b0f06030c040b03090106090603120305010b040f030807021f02070618 74
    0x544250300850100c2d4418802002a41900d48080c01030008000e50f041900c95102e080a0005051440d007001041b07003842241c5003900040a0303105d146c040c154009000290340c00422515884900c03035080060803030710a000a00040080380c0340440201c901841c0103420590300c0796007994554090307c8040c1e6000f00d40032030124000942d03500c2294541c14001000d803501c44107650703903c0242c008444d9280d43c43c1d0344400c031f081c02c2c540007116542010011140303146140342082504000d0140401e916080051003000510031500075440f0a883c03814003644070741c8440c2e154500c403010b04003598406001f80c3d85008546100c1c10500140c80c0508002c1e40f4890909040c4403916803a03030002031148020359203901c000280e0700902c2c480c140c043c5004184c844c0d403501c0341c4903020341900d40690000c512110104410400700707058240348403c0e41d512030b25655940b03440d4000645c54010740d400207942081d230072101558450b00040c0320030440d009034403000c00c0101820ba031034040c0365081c0310324042c2e803e10030341e034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 797634514 1250 797633264 797633267
    0xd0e1e0406080a1511030c0d050423012a0503040b040f0f062903120a050d0f091a0f07050a03021318110313020607050a0803190b030109030e01 63
    0x6819409002a100154141c0e440d00210b16044004000341e40003410600e101d426002103008800101080b4a0f01c10300d14200500c0254040c4151400c42c02ca460b95200481d041107200c0c40c084041c2c281d29951070080322200120140200342050f10340c4000200394954a61128030564000c1504006445030743c1103507039036212485c041070000e004070303160034240310702800040c0c001d11020030b4a070145200040740c2000d50100c00d142610802c2c1d1401c524181ca6121038541e80001d00262a40030b00344005880d51b0702d901e0150744900400c086550200c1c01d01681c5041302c1800c0c0c0c030201c0d4160141d0409641801e009040002207a0f0503103003003003001c50100005139528040c000421681020b441c00500e048a007440d4070900380c069030440c6452500345414003920402d5806504007200400345580e103142021000f074031084001c5440207003e100c022824078140181444410680340e0040c5e0401e07503d180c2017803281c00c2448000e030350351115442c0c034540c50034909051180100640d89034480d00f02c0030880400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 797635764 1250 797634514 797634559
    0xc0b070201050c010e070e010509060d0303020d020d020c03030702070e0c040302091b070507081006180506060702090f0430210c0c021e060319060f0b0c0d0e 69
    0x50990510000f0400082c90307034400d1003100c46000e564405444000e04042c03650407400b0313060340101d02c40c0e4010028803029941b00713a84038141640c1070038010b07611682d2040c031001a0049944000b9210320214100c40d150344044011072103007280e542504c0d00d454032000d0f0920420b60650702a6070750322061000707000500f81003614981140170a00c51403202c00f403c00c1244400c0c2e100103400c8034150010902044010310812526400582402003800203d0405074040c024844205182138117649800208030961138a100f03c6000a4018120b0003881c544101900901002590200c50310035205903409804214441805c1050040c2c0740d0303a03010101e040a08030b440703c2ca03e0980c54a02001c1c000c40c00540304562103203204584070350301d40104c4040c4c42d00421041c074105403081c1003080000044050140d40364001c0360f5201010b512802c10484c64195400010f00254203d0340c6118011403011641c618a07001600c0c00b41c40001c1244d20480500c0d204984503212071903010b801621154210500398003d48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 797637014 1250 797635764 797635777
    0xe1509011806021206010203090102030d200a0816090b071211060907210b06090a0905030412060c090b1c0905030a0e120c01080406020a03020d090809030f07030c0b 72
    0x10004200711880603441c04440d01201002c0360401c1e40003c0411602002e1006964046402d0001c1d60601365800c0000c0d41f288115010900c040d540c828001e4884907595620f00010350340c07086a01c1d120582c990001e04820401c5e02c158001410300c0c20742c07601d26403052003020103481241090a0520259039500030102c0a10b06040b414480f0103007030030220782c40412100e031090b180300004040161402040600c407840a01d0080d070350040100304c40700455401408160008000c5d1800700141d039402503403800908500c88024414000041c0008110104558031003440e4001d000420044034141c4069403102c10300d2044150201040c040d9000445050143c40302521001c400131441503c44d540303085c116072001c1001004206c5000c2206080d00b05581c411800600c8400200340c1d603c007140020f0302901005000600c810b80005101c2620303032194059803641403480c0d109008000c0c6500e082202ca0f00101c40c418041d2080f101d024881c1ca40c00149541103d4024031068099824020030714103030750080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 797638264 1250 797637014 797637031
    0x190f140420030105010e12030702010c0503070507090b090c0705060c0a02070b030118051e0609061c0f1407142412060411030903390609100e15 63
    0x1003202655526028040c4580701950181c241d64075030400001405034003101c64203502a2110310b2180042c1c01002003240c0101e502401c210f40812001d10f0480c0c81c600c0f4000000303050340900480010484050f801c0000340c6001191100590364450381c0200b510b001d62180580b103584510082148184010000c16003040288191078515440710580300103903100b039100b211200d44d070210101c51079030f0521a41d90001c0b00c0040c5c0032840a0384680105a4040240c43c25201da4841004540340d0f44e242601e4901002c01c180150700309030600c0c1800660350491210a0710003901811811a4070180401d01c039042d111104411110301c1408414040d8a85130a62901c44001140c1c070640f403907024400c0500444880d071400c480080c6030000502056641500b0450601c44c802c5c420b0010070b900c0881956014800c200c1c030941e24030a55a6206503071407031004401640010049400725400010a81c24030440110702100c83d0b10352040081001c84195114900554211581700041403c440c41000e4020344032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 797639514 1250 797638264 797638271
    0x905090c010e030f160e0106020c030a1203060f030506040311070614030402151b0c0406060f0c0203070521060f01060c030c030203041a0c0c01080705040b2b060302190f1404 76
    0x7a18a00c61402000503403802480322495410441c0c003031b803a80801d01504151014120200e10748002c01e030307030b04070700200204803841000c41018914860345c0102c0080c07400b041d4140308190f03079003891501c404090b203042d80000c421460382c8204400010701e540c00c54180d903a91044d80e00141b10415203541010f4801c90780403500b1410181c2803404e5070090221010b2054002107602c43c12410f162910441124903030040741031100c200320080e0400381141b0f4141c194107200b80410094400a42820300e540c000036030060300102d01c0016541c1c1c2d40c841044840c00c0340204e4159481c0d9480c440c2c035210b000d20036000001c0c1000540c10010b4880d002d580307030007842170044a0426032101c5181001e5074010813110850000810b40e07000c42c000411070410f03201d10038240f810130741c00e01d030034000c09034450b07800f0b5440e4404002a2490f0b400480c9607949914140d02550381032140ca4075207400c00035020350320007644107410640401d040c400750041b40b1411603080071800301560703251a0034070324504520308547e46d1041d81c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 797640764 1250 797639514 797639533
    0x15010f1a09030a0b01080d09350f010b130905060115020a210801140306181009080903010c0504151b080703110d030606020a0f022205100905090c010e03 67
    0x50030041c03c01c1c3da0784a08142041e175810f10340c40501c0e00041c10310741c8040001c015404c106c09111440030311a18010a1485146141020740802c41281d510381491107600c50881c0510f00c2c01c2066008441c0c4400c11592400d0113151405805c040c0c0e407031400c014007ea0452401040b030188500b4801150300c140d401594030008640d22203000d11510b44caa003448042945032081c0c80241d01115042c00741c0f00c0940d0718402c4111080110741d60743e00082020703030000c51039034410385000320802c40c80c140501482404d01025130715103400310043e00444c04c014069070034444540d0405000780150f03000d4800812001c1c1d2080d0100781d046401e9001a86e00ba0b44e000c0c01d403a44c810105540c44024203406009441d0403000e910600f48861925003603124034010140790840910a4a074003080a0018903080065034030001010700016007000072030740d03140c403114400030020070300582184c028078800d41c150340a20b02132036605c480c500141d500482d0451038903006005c0e240301640c021031204c022400080e049400d000c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 797642014 1250 797640764 797640769
    0x12130209070815040e0705040f090b09030702090c04120b070207081608070e060102150402060d09060504111f0810080d120501080604021f02010b100309140c0a151116060215010f1a09 80
    0xbd10640c2c80c620380d0382002544c0419814041e2300c880e08110300b040b98500d400d1a02c03100c0c080072041050003c1241f02d89501144551780300b04242c0010b0028202aa0faa4031010400f42581c0701162050b6130032405840340c000b0b07616a030450014800d10040e0044e000041c494521200a0040244200d90000052205422051080c4500d40140d44160700000b940d0070b00b400c203107241d4410350f00d07014400c0c0c010741e41400c1d1000102c1004030030001c00b41005a125110002030107904801c54100301407601c10301300180d0840d6070080148110b82c1640d0302c2044141d0300c0d286103d49580040314043d420620b600900300d60414094010071140740f85200000307868080314001040f40008846141c0041d484030032407400c0c4a1401c491b0580014541c00400c08041c003107012406c81425481090341003160820800348907800341160282d0052032200351882c0c400c5400c0341140789804e80c02860010310503410040c506210424005041c0e40100b0148080e042c07801601c2c0c030b01ca02221444181160051001a280d42c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 797643264 1250 797642014 797642033
    0x1b0d020c0a23010b0f040e01020904050c07150b0114090f090718051806010c02190905070e1c061509150e09060c12130209070815040e0705040f09 64
    0x100d00c41d03900d407801d00d085104005882c104100004000e41d1520609083c0b0341c1c3c64101001c814071051340c022603025040c00708180240101e00c0c119421900301000c10524500380e20061006a100d5258000b8054100c04284102c4400c1a44140412501895030360000840000307003401040003012004602503500120b1340ca14026540d90001c600c0303030b219507000821b00240c0071001e480301b82c2d0301c8501001115280446948003810b8503061090040c07540c0306540f110000070303500000c5d158000e03042d9903484041c034009150444503a0b00207070440244684501d03142e032034812100c800c3c0450342c402c80e5540c1c480500810365504245035000f4403035030000e8031141c0c6000c0d504015080c840740007182450030220340300320000107111184540100b02001017070250030095840f0b443c09401e41c08a203980b5030f170302c1001d402403201c0003039881464070003004901588016224400c1c2c190010200c040c0d0020740c02c1c0401d540724560494520b4000032800d002d035041c29441404000d06141c0c012030415142c3d25500d124 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 797644514 1250 797643264 797643283
    0x80702120d09030c2306160b0106020309130506030c1009090f1509150b090301061805040c0807120b0c04150906082202100e1c030908061b0d020c 64
    0x101d01e00003000c009001380b100c0f10000504008214000b000100000014140303100c8602601c9488080351194407114504034840145a01250f071a030503507140d41e40a0344d81d0b04003034040c6100f0107030b481056000c0d5442e07000d8603001c2c01c80a4002e01c2000208000c0103654200756a0380e0702003081040002035454540d014040b44814a41d400080d2913490342004c680780185608102d08490510145400c03000b1305c1b01c4444101d82407804095201c04000d4000b0740500ba255120050700020540341c61170542160307000d01d000f64455a000b075109603450305680e03110882e92064801217042100d42c0008034040070121903000300c10f142071900d4541c5841003003002404803c015000520035620611840e40c01007030391030b001903002090103810510301c00405003c07244504000c0c01041001c454150681c0540194140d2070f40090980c207000550101c281102030b01f140054002840071040019610b1000c181c00f8000c003092415440350070080c01000c003441d4000c051000d40c1c540e0800c1080d200e40030034030003001c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 797645764 1250 797644514 797644517
    0x316020f121b0c33070804140d030203181c0803011d01291204050f01110702090117120310060f1106190605060f0c0d0503010e04080702120d 62
    0x4466400980380848100c6a0310304142c02d82c420441005a40d03906104090a40d00091540c0d81107075640d850803840d844080001850410046840820000d4030301c040c1040e030320300c800b1024040241c5010001038183c401d1020300036800c2000305110108003800c80c16040765002e0408501d0182c2410b81c4040d4203169241610a284040014013120715149503e000c50710b1315220b89222941407818120f21411051070800310802c4104039029184054000d603603241c0c20b44d4003490030781d02c3d26040881c0c4514410000314165441e080304040c5e0340034500142c2d02c00c5a005002900b060303080042d100c0300100080e200f06100c1c402c1c003103e024200001001140b0400302d030300d44409294503181001e0004c088141614040c407a84152012210f040012010f03440010031140d02e4505441d440b524006100d41e801c01504030340001501402e90003803030010306560744007100712000c1008000c0129a103000038003d2142080c0303841e012402184032107000e00441ca00091410f042c0145100b01585030034a400340f13060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 797647014 1250 797645764 797645767
    0x3040602070c081203011e35010c050301090e0304050303070f110a03030f1d03030d0209091f12150615090b042d030507081e120316020f12 61
    0xb00300704405080020070741d1000402202070002054481070005004603141c1080d241c640074601c64640c031803c0002c0807403c10003182d1000d45510708001c090810304e48031003031406482201040c0414483e10b86098840c0e07840310306590a04529002501c0380b0210303c80d49100074070001c0f030710380e806000821610384103c4030624440e8040c03401030503007540140d0781c134800d42c80070604001003a08400b251300b9221080c909940499682d1000007249410032170569014030001c070784043c10400c0e550040004c07200c100c8040000d03075245034404180e424846180b0031400c20440007080006c00309140300c2c2040384038102c4900c40f80f03903e200040403120980e000d0031035140c01c19000c0e1511500107013684040d00414007800d140504040c0848118100110f0007110070350b00000b91040207007002503142c0615408004d42e600266903650459940d010741c8441d0408a4000e10b903800354003400281100e1141413400d1182c110364400c4541c48219448140c0700007580254100d15007444002c2c408041042d144c5101306 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 797648264 1250 797647014 797647027
    0x60f0b031909212d02100902010e010c0305070204090b040201030c030b01020318060d240b040e07050f0910050406020d1106060d140f01050601034a0303040602 70
    0x80c10701002120009599601d00108000440c02c0948441400c040083c5406450f0b842a83c0440d90200580c00a030035200c02140c5420102c81c0c800161040c8000350341c00c0754280c02c0000b0001c4215000800001d020400641c00500154001e08100600030b0103420210306140c0680c0109091329202c0754100c030030300801001c0004646e00b62160b501102480d180400c110004140041d580380300704c20411102c0418000c1c03c81c010b603030303100032515007800001e02848030721a40c071110242d0a50300e0b46003010305c8400300710214410200380203880403282c0509009003162900310050303420f0b9008a805200302c560800c1448000c0e11450f840c800150004d40e1003035551440c0a00003801c101140d1891070070884410780c05541e169000441d40d4100400701c43d82040c83c9101d02d020440712800510b9480e0500442c03007450402d83d01980308610a501c20380b002d01c1259031008410a80031898040507107205d021241180640303040209940000300c05080b0540780a20400349c10340342d6041160125034803600086c80 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 797649514 1250 797648264 797648281
    0x50409061404110a27080a05010504111c031409061305010f0507020d11030313030b0103120f0221040b040305010204140901270b15030f010b0406051b01060f0b03 71
    0x80088043c03e0600650a0446081d001414194440c0ea070740c4086100400310419200c0c044540c20040100c9811103001182d940b4046002e084103c9042c2e4071a4282c4440b0881403d200000400d84240030011120700030013a079054945403003480818a8803c01880030000b281c0b1040014402a40820400790480749080b00041c80107a2080144040040900600006031942d000c82e100e0b16074401c01e000d04600c20200072034910300810031141022204002c00002748081e4a170054140d0740101036220041030b80010650303820340d1003521000103922480809a6151428091102c0c00440019103071805d0b94030003e0f80b0090700560070690722650300080c1003100710302c00e91280301090005e480443ca03075890040c00b9104d48014440310350348884401c590340010302c21644000e4580c28010010600f03056100e20f01b840c0c541084440104030b00c08207002140c40030701041620300312507180d9540c1e0300d4414400c0c80400c060301b485c0b84c400280d42d26048046660ba518205130405081c28690981e02e910f00b501c01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 797650764 1250 797649514 797649521
    0x11e091101021207080706020909011d0702010b0d11030a080a0207050405011d0712020d110307030c0806030c330705120c070303141201090506040605030c0d060c050409061404 77
    0x2600d042d076019841041e150b50360b060a854416400c40300160702c0342c6083c14464044d2041d1188590f118400200125182c5100210907032040018041080b2554480200740d0886885151440c0c0c049042d00743c0000040380f100365826040c20103030507104010020b681704021608085032280240c1c1003103500703201500b40f6204e05401400c9001c00a1804409903c680e80c190300003601100800058080011008c0056011545114164881040001c1c041100742c0400e4106699807c002414411103659103031103098014060314005024040010785241004401001c0e01d00d01001c0b945e500c603100b810043c00c08021101d0807000d4131066034501403481c1503420501c01e150f442070004011b0110303080314000040c00d50305403589802c118140e50507030003951805014031a80c202010b1a4000041090400d5400850041d10709480611800e6299020140c50b0a0103210b05504441c641064001080c01c50700941d203c2c03138403810054030341600d40fa5010207890090300100e0707119690240501d0141014070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 797652014 1250 797650764 797650793
    0x91c020f100305012d0e0601141207090e0402130b13180309080703110613080613150c02100207022b031202040b03070c080f040e09070605091f02011e09 67
    0x5017105c00ca01c0d40e034040c0c0241202d0340111101912881c002424507406000301c68019508041510344403400c00348020980842129404002421940009144409580c10700e015030390003800341e02400010101c0780002e00001300d2007603001ca1220100c0d055014140708040045460124085d045412800d0280c500c401c140d000e052a035010807010004203600601d0f442d4408800c0707a0480d564100c01c400d002c860021900106014000d01082c0211240b01004407000c1d240320f0b80204001e0180c21290104450590070000c002d6000b800c03c0c15203040c0c4960050120038030040c2100d591400090600a41c555403552030303d28216980d600d80207040e0095080140c1d200e05d280e055141504240300026240405400380c4c061151002c030003400c22001100340d441034039516070615100c690321103030000311031000e0300c000c1a41d005008000c2016407041c41140c282d07520240a1444418503240305000c0f45600d8190b100855507124095000d01001d03070b040c4824004030490200300c414150512060610241 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 797653264 1250 797652014 797652059
    0x30e01230d20090109090b03070b1809060406120609140601080607351009020315041d0604031206030f120e0901080606040f0e0a08070b0c091c020f10030501 69
    0xd0103c890b081ea8028075450a8611540001c2140c001410100f46002c0b0290440a40316602090034400c42031f07210000c068000c4110b9034907680e912110309000c00c4443d14001c0c00c118116118170000446c100d60000d401083c0f141c1e481c905000d40050415007001310a03040703000503401000170700507850340c8001c8415821481182464280c000c0010a0041405000401e12180355040020300c1e40701c410060000285040c0c032041d0754034a80700d45c081c5580e00780c00420340d02c55864802140030305d0003a0b001071001e40001000421240e243d41c0c8003511500c41019103500c401c0e0f105c800100c00904e000c501041c50078840d4509070700c803152140001e0300b06030340c8450003070040982500401406000113540c6410410030385000604400c3d43c00e06001805e0760140b01140d6102d0942507a003044411402080c0c294000c00700c40540791034825a8a1652103035106a90340900f260014000242610312020200381c4004c2030715a0f010401c0003c118691068851200481d81d174500411601e0319141c1c0309a03454209 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 797654514 1250 797653264 797653267
    0x1002070506071e21091407060503100512030d0204150905040506130f09051501060206011d01090c090e310201021005060307051c030219030e01230d20 66
    0x4680503d514007403100404003000340398a030208002c0c0030f4a10f140e94803141c0d1101804060050f040207100c0c84e00c1e03980d5030300c41031195200019040d8410020380b4001c1a40d0031419642c64941000c00c00805503000081c0c0c0b0900080011512030140e0b440100700602040c00c07940c0155200350f5003d46841d1043c4e00c07443c095400c1c0010000d041e5500b0b82401d85128032550001108207580c030302d0000500c5012001011485100c142d5051800c400c2e00c024100d0b28250b08071940390382c9038a07000c074070f0701a1205004581c130f4081006202c5022030307400c01c1805048500e00004000d0b610000c00408003002d0360701d01ca40040d6860718034410b44007444100715116032000403080074221640002c1d82d039000c240306060055a148040380155a0620900000b0440106081d03440d000c500d82000c0887e80b041d0040b8058464000c0e0010841c0f10707602400030b4141c043c2c460141480c501001910500d004070313221040700f4454000d0712031500b0707100e000d030111039440c01001990702100581405412014101d400e0312040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 797655764 1250 797654514 797654537
    0xa0b01030c051215130605091305070b0702041e050402030c0609030703080d0912020607030e0a0305040603020d060f0f05040e01201b06160f090e180708100207050607 73
    0x8000049402c0890582d01640f116900c13140c1000c00341e542403c400c0c0e481070203240c401070020041d400010950300c1c210b9500b0480d4607000103000000b000190000c0c4a0b0b00220010803d20035280b001d01140c1e4009400400c030061201d0b4100c11803119000402940d07540c0c0c000b44019070130100861f1005450a440c403d1501c046000000e984d00400c0c4030081030200f00261401107106c040c0c0040d5001d903400760201944100c02c0b403010f900c40d10308480c400c00080c601044070080350000104403042036010f440e0381e458941840c0044000c0c0d031200401c10305050702da08000031042d0311211404028596080482107140c1418100010380701031105202c03d5030705004000d4061040b08600d5940c1080881c1c0c2c80383e407194200c080d90300205803410308141500410007040b030040c0300000d00d00c440450598a8100e042c20b40c15042d50074402ca40a884141e0607943c0010b001000c1170162411200700c0c035000c481c22035a45c4c80b50303d0300d04000301100e0300003280c01013140810410701300b101541000d81d6080c81c000182 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 797657014 1250 797655764 797655767
    0x60e0306010311040209010516050a1a1902030c09100e030709051015020a1203061505180103022109070311150d1e0f0507020d2d1707080a0b01030c 65
    0x2000420345880345a0004400a1a0303004100712004481c9c5000c3d8a41e132810a400d002e600c6034038480d0161019421924071a61340074268000a1141c0070050306998901545280e820081d000141100030410080200c0d20a03691200d00d0b050741010207940e83c54a03030500e0002c0c9420940b42d40d200e1000c40d0709103810b0064500402140101b901c2020260301d6000c24a2441281b40c500c0d4054040e0a409424070400c44059054001d00240e95541540c10320244c16080211040d116410300f402d41c43c4000782e0401341a41c41390300108000c40e2390340329404406109044a003016202501c4503507955006803020020008100d00e401751580045a008c0200307040720300000b50714800c00f4560400166201c100700303a450702405060044a4051400300801034200c070010000304002d0b5024405842001d0f9210b150328481c48449000b41204507580720a1242031044a02e49406040710754240301e1100401c0b0f0600020010b2140b0628143d5036261450030303c40e15440403201e40b08030707041c10541400c20060000e07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 797658264 1250 797657014 797657033
    0x1020a080a050d0b042c0f0a120309080a031b050406170903190513120519170309010903030b090714070501140717060d2001090308040603021201120c063501060e03060103 75
    0x1a00b080da040c01c00303210009e04800030a035190000b0015107010481d80307070303c95061788840c0441ca08840c0380700c0c039010400002e80c1c2d02d00032031241d680010351031100540b40c0440c5c42c1c9400c1d0040c003844102d80c00d20388a0003400490040441d045000a50041000c042c91814025400000d281d810f0101c04101e00c40d1b1501d81d00c640e41140442c900254601d00b0354100541518505c1c1c0715015403d031680c40e800c08515040c081c001140342503000a04216016130300d0f00d0000110340c09400c1c90b0f142d0103640044c819411110b50022031040d43c15541c0e589011004955011840f442032006988034903c520002119421012001d4200f07030040b070303900c0c1c840300000c0c00c00150070b83c152060381c0002500035941f400407604004950001000c000c000702d0002901c84d0142c01400c102d0140324120740240ea203d0a07400403501d19058060b0080102600411004e4054000821008001c4140b0361f240145894071540711603608415018800ca0880100301c45580460360304110a81140901140e5145440b0800e92 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 797659514 1250 797658264 797658283
    0x1d0f010326090a120210030c05090f010302070503040e0603160608070e1c0501052a040e04080d0504050a031403100e0c0706060b1801020a080a050d0b042c0f 69
    0x300340107894881c00c004404107944a018004012000d115210724202c0c03111418408128000c514024100240502a0240705903420860b501c02c0e017840c03014030401101e81100c0c4c0926041c03560801103000410014030042006c1c255a0026161714104002030501d0700c1886941148209051070703041c0b100e20b03400743d11a600701e41c5c0c42c03611640c00e00d407920004003403c2122900c811980d0080b041c01d82000019003000e48101100403000c11040c040e40010660041921030007010001d080005200c80c40203041c1968115024000031401c0011071135602c000c46100f41c900740d41c55071002000341e04165101603966131034801c40c440282141422000039500c030b1801d00901d1440110302001440a0021406850860390054018030146694205242c40ca60103550320004103414a0804101940000b4201c40310316440580c017840c14880e00804c5441390003c2100038110354507035410140707561711070156000c850134403101c04024010b103003040721010000c204891a00c0d00a90076802c030201b00400c0c40080d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 797660764 1250 797659514 797659553
    0x3180708030a03090c120f03030614090610020c090403090e0105062d0d090b0603010605100206010308280e18150909011113030507050103020f0f0c0a050105011d0f0103 74
    0x10707213a040b807a00742a403000c19005060621402e02c03c24042c84004c1603c00b101d240682c82c10040f0076141c81d1002c40c040c4100c404150084c130590003180c0d450503c0042c50515262034410b0762030742e107090b000050518200751000e03000650007640074440c0d201c80c5000213005003822541c80c0d28110710440141b03c41c6242e056903041e5001441311110740703443e04030211040015840c1c0c01b0021804945400742c15200c0558483d400b961038900702050343d04218502038a2455070f90000c00300c0d82c1c6190b541203140d41c03040001d101c2000c950ba001100f40e00400c0700340c8004107101d0f01c2e1080d0380c0900e203040c0010701103030701003c070941c1d0021003e10101ca180a0364810105009840300f03002503882c8081c0c0d50140050b0941c1d1030a0780301c00510000c1440d108264402030f01c2c85070342a0b806c480c0e80c85e4011400e90298005101d0302d404108001d0900c0c10156000381030441060050300e0310440c051302c80c50301b1203409901203030360035030080b00b1007039800740790070344280c0c0f00700380328503045107541140c4501c0c1c00d013582c11140c0e00c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 797661870 1106 797660764 797660771
    0x1a060c07033912080c07030503130608060919090c1d010f23120c0a170c0402041208030606070f05010b12190215040b0f03180708030a03 60
    0x20100c03222601d1685014509403079450145c0d104003c0182c10344101d10740040041c006001420605100320301c0f030014a4a00100504031903070040c0f02d18410325440e0101305c000c002010414081540c172080c00243c1402e80d00d0a950078089a800c5011014802002c1c05009480880743c80d0584181ea805c03003044598920403050003006440484c0d005640c40455010581440300c8181c201031000300440e90300c5401030f00442d13104280c030b03008070020307000041280358042000c00c4500c0b8a01c1c402d0b03a0441c40d05240810b500301c6071603081c0c00206003020000208985940c1c03201900d002c690040007008110300d035480c2c050300820302c400c880d40c040c059210109003411004100300000606046060070442020b0b400c201d00704105108444d41140c05000c01309808a2260181403841e0b040b0b82d02d55603034184040070611450b50540d02e14410b612000c2d0a0209000c0801510300c035008504010 = true := by decide +kernel

theorem cover : BRFrame.Cov 797482014 797661870 := by
  have h0 := BRFrame.cov_init 797482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 797482014 ≤ n) (h2 : n < 797661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
