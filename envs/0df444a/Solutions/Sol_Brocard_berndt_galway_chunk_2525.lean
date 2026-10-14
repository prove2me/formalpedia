-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2525
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:53.213992+00:00
-- url     : https://prove2.me/submissions/d357c59b-176f-44a5-96e6-482206eec66e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 453956834 ≤ n < 454136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 453958084 1250 453956834 453956857
    0x8090108100e16091a04030b060117100f091b0c05070801090b0103051c0503130318150201051006020a0803060406030611030907090c1704020f03010f0605040e0715050a14 75
    0x140c4000c2c003c0003400c0c440345a4080040c2511081c04030301c600440d481910304513940070210040c640c0326000144c4010300075204c45078039605170358100441c5c1880c50b04454100c0340080f0069000e6500ca500c03120030f5a9a42010f01c0888000a21082e20300340314041446006000300c081d00c1d0041c0c4c17904442c500b540c0c5002000d0341e982d060b0f14014000d100045c0080399400021703690550002c40d41000140c564000200355030352110111041409260040b0800700b009200d81c0002601261502414900c0a1541c0ba91000545c0307004005003240065030341c058152400c47e0010415840e0300d80e00e842c102d600040032031b9041501c4071000000a800d5009424550312243e42c202d4603450b00107030052501049074009040a41000d11103250701e50000d990360814105800c88264945d0389002003144640344400d0113405d5031030b044060003002001d070701c4041960011a028040402e4000509a41e180c45014122103503a9100f0031424180c000c00c0207000b1a02036090948603803083e10082c10050300003666949 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 453959334 1250 453958084 453958111
    0x60e0d03150905060307050909070f0b0c0609120904020a0210150512060f0c0a110a0b1b040b0406050a020a0602042c1905060d020d0f0b060306010308090108100e 71
    0x2120412800c030307280003402e00c03003004000750302c0c00400090f03481039288030b601c0c00f030b0500701c0110350550b00c1480010081c00040d410312100507542c0340c0c030748407690100c0710701003060041c0004111580401300301d90412282c0700c040320742451840400c000c002d600101c00103095200d080d0020800407914041d0b003600c41042e01d6011007170343c1381405000d00d005c009040d441003a0000340800c429010606003854000660f0707801d1546078802404191340406030000070300e00a104450032402001003c0c00518482d04101c00f0b1007000d100c4806100e4602d004602076042d400c0350522042c8034182c4200b0140c04207210510482e45002d00f261a040101d90040d00400451b122900d03061079811020860115600b51380002585a494010700341c05c510040002900c0090780c548000c1140b44d13858243c1007503102d4004018058940d45c0e07242c121625585100100c0d401402080024064940412164100c0e071700300070300d10310708107100740115400c4400920010219001e45000f141101040d1101361140b0140c80106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 453960584 1250 453959334 453959351
    0x3140a030221011a0c0712031403130c05010201140a0b04180f061415100909021303120810030308060a0308030403051b01180201030908090306130b060105030708070c060e0d03 77
    0xc80400100700e0100c007444c0d0041091480e000d00009401048607a4800000b01254951904448038405c0380440c4640007004402c6c0100c21404464800c4031500c81e51905010f03981d02d20059003a140302080c40c059511070400002d40624085e002820302010003040054240e024140344020100800d10551380d11000951400c2003003aa0b1188607503244030964001c1d0740303140c81e17814420340020300e90340320f0f0003000c01c1e056000c611070007801a50f0242c04072440070741d11210000410103580181e4403060f00d10420131f491484c00c080c0901d00c03250003520090114010a0300710744043e180700d43d0140031a500b1810380c10001011070000ea01442c015071003540c80c181d031440e0030082c003000d12840a400c0299a4034001d134464800401d21451218180c1c203090100e010141410400e41c14011802c6458150058008009104140710218540319108403c0300c640c9890b0703140115458003080700c050700440c00050110300307032501500c00b2650740f034414400403440c070b1100015a424482c0b08004000801e40310540d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 453961834 1250 453960584 453960599
    0x27030d050a08150f061c020318010b10080f09030712090806150a1e0b070807020a090510030b180d020c030f3c120307140703140a03022101 61
    0x40c00d821515140f4000000051040003030303003a0b5205101c40388541c00000340c011104000b480816000641c0e814211b4603403901c6030a503c5240400d91031003046501e04419131019180c804040c0400d5652035590384020f40d649462001d1208011b00f80b42d40fa40b0040c415000080e41e45440b861310039aa070350f02d400c0320910b03141e00c017403401c20054643c0e48540e80d008035940c0c89440c6c0507110012645100b4411170186094000348147c0e80d40350300302204017100000c1c0203040c4518a4000c14032244252001122195501c862504486043c2c441440b007079000c020810108020f0792120750400c401e9441419090000ca207524603040c59000c584000d038200d40680c01075854103002c0404052151000f400800d03c03027001c010f150000072500c1c11071a00c1c1e190040c11542030003440d452201c80240c81240c10b44c404011503c2d0454004880c0d020000f0f003400e80c1c000c043c1d01080d041e5214250b06481d021941071101b19050142e030012550701c002c142e4240b0401068001a00c0040ca060640301104401c55040c07108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 453963084 1250 453961834 453961847
    0x603020a051002060a0f090b1305060f04050705010e010504051905040b0607030c1403090d030905030c010903030206040b06040b1c050c091006080709090e010203070207080607020327030d050a 84
    0x881071007962070920001042d40c01180c580e52058103403c00082101019059100920a10718007505005001c810451000509425038035154012030489500f55129240410a100200c400403c243c001001c10815540039030046100040b05042c01400d15880c1c6003ca082d68000011038080940600e00401c50307400c10340b140d40801d00c17060303803054980200e039100600500f4003500300030500c01d020701044403210420310aa036030789000181020244865030400400700c1900c0e00441e8401e00607070400c4e114945c050b41c6d8100450f540f58010b4003036603076203468809030f110000300019045601d800e420f48060345c464046906880c5e115040e030703006803142c0c14074078600401c07030800034060b080e80020b105a008070884180c04480d61450070390b1143d515100115165000c0ea401070200a080a01813545128190051031103000c0c254215a021565461180c2e9504429606100035810810580c603003148004c0199031040102540304111080103004285014000c0c00c00c0380020310301107181d40e11581c1c010f1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 453964334 1250 453963084 453963089
    0x60d140c09011b0204020702210705010c120810080f0d12060521011e060302010f09030803130302030c0601060305040c080102040f260d080a0608030408030301030609020d06020d0603020a 82
    0x110054204408000080c1251040f410040c0040103041c07040011951150101d405042e4081c01c03424419143e0b000c0d40d24414606800c122440c040c00c803010815510440310800e115070040414812112000410f44050070042e117614202c2d5017030040400c100004000e444280300000307004116246004030700900400788070310f548080600306a020012a0b4a400d1400b409480180c51800e4480080004a005001c00010a0006074180c40c00968210442e4812411039000b80c9543c0f004417890310742180c080703406010003460108284003180f0700d4100c8045078100b0f58424012a0303d80036480d4091450400c09a220307000082d01d55003000104040840e001c401084920000d6091078104410717540e401605000340c003c607580c40d02029907890a21817422404e8032540058600309111040e00400748141201e014018900300540000d016000004482c1118070b8800554216400c640d02d40001c3c280728241a41d00100c10040740010421a01c0203061101259030002442c524601c1070040c0f00d400369 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 453965584 1250 453964334 453964351
    0x103240612021305040b1c060b010e03060601020d1b0602030f0a0c05070804031704180501260a020f030f0f0f15090d0309061b022506140c0705060d14 66
    0x10f00c980480c260000d0300e00c41c2942c0084901080c518429000b10b4485d5001181900480c000145100203110a69002c6405508207980318a01806003200381355891314190b0719603005a0090314403003c1d6620506d42030500007545103540d543d0301e1a548804080e40c2054500c1044180741c54140b090482e0140300c0e07420b0311f1880f410500d0030100d464035648610702641c40054002d460341410f0b1a5182c075603100302c80141034452001c0204030307407991304003004120074000c0d049481c908460158081e040203003410300d275a0100000340420407055090100d4500d180c0d2186400d8403c1c0c4001445541080c003003500308140000003801d072503c41d01815454400c00403840f000d03207001034007440720303491010444a030310705c0075030402103070288207880c2601c010140c6042902d0b0491104d0342c1030760313882d50100d80d00070a0800c1ea04c40030b0781e4131120711400c0003400301c0384240e10108416907810f68903542c5901c09002d0004c4440281c1da0b5459441000c55940d40c0033321203200c5420b585820f40e400c03000c041100d054104584 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 453966834 1250 453965584 453965587
    0x19050d05011a07120201090618020301060501030e0d030b06070206210c07110607020a0f0b04060908061e09010e0109080a0216080d0c1412040f090b010c060506010324061202 76
    0xb0301c0c0b8220030384100b96014040c00c0384d100100410500075044208802c0d88120104183c015034078841c1031855005000305c0c400d50030428001202e42c4a400340c000c50f00c0004000d41026141d802058008142840510f07030020414407064000da84c811000d00840011800d03c420b005544400307045020600a0451040450500a09000c900390007507100ba900015542c09a44803040d0000414655a581c440c01c50b102c041c8401040e55101d5030080e1007187c030390380c550348613841c1c58060030358852400f19041540e6000d107540f024a241420620681c0150301d01000203001e4502c0781c8003500391000c4640985a21f03000241c00311245a040001340001c60603844220f4407642400b020b15154014030302180108610214050140a0f50001c1c400710304856000b200c2e05003c00104071189900540300301108014285c40008001c4030a004401018205030344000360b0662030750b80c02008000140c01c1b06d0401d5a0740c0b441102c0420580f00a103400f002c14050380c0211481c0002c0244002c6c46d000c1c414402c20700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 453968084 1250 453966834 453966869
    0x90306010905240d0b0103030228020f0f13020f1801030c0806011427010e06032a091e09092b051e04030507060c0f1719050d0501 57
    0x801c8200541c00050f0f00900100070483d020000304555a840405458500701d84000001c040d000140030100c00c0700840c040c05103901117083c00a1010428102a41001e601c0c400b400461606401480e00303003000410300e0220038192618901260030008030600000c01c002141d0000303078030030256130324028401d20f01444042407450004080300d4010340828103010500c140d044029400e0b0b030682d4160014092021250a500001914201c800c109000c0c00b01e81c0c0c010741080142860f604480c40740b0810141503000040408410200c031001018101c0125001d025a40d415a591018484440c0060340038030030658032714041001c07604015202d08440d601a01c00c031034001e182c00118402000c0c0030041200e103d95088002c0d40d00344120104402030840390080e5001500001018100741c0740100e080351300302900d0301001e84400000d000d01414014042101c0c030005900747c0f00740b000f100051b0380b486041c00b27030b03070f4801910022030fa90101d004034002245800c0303034842ca0300c2041d00405141918003131100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 453969334 1250 453968084 453968101
    0x403020d02040f1803080103120504030506010618090509010506040510230a090606111015031212051503150402060a05160b0408040905070c020303310308090306010905 74
    0x40d03400d0002405103031107184002d254600c0d07622412102041424806810300c040c03034000c02c0c00109010413640c125509941c0d031881032081d42582e054036031000043c4030310790800c00180e580e00b980000300c0d03107a00b000e19004a10700d0002e0117000e014802050001c241c3d81840701c00c06c03059510041070560354031100e2400b004810003012007000749030351039140c082c08429210081484c4052580240c0c0009040030400103e41c0d5101c03207800000c42c040400d54070702c50b5410200a041c4e5003607a8001042c8143d200301030001c1610100b00b01140403a41c1050600c02500303240144c1910300c129040c013852a0800c55120b03980c1000e0200b908258414804010940f60581c0000c07054000c07032907441c04101c2c010486c030541c01240042140400c0e0407a1020000745068682540a0740c054051400b240e810440410105401100700e51701055000340030310309082d02141da130035060003e4032001e0950828942e5028000f0b1009160078043e43c00b4081e81580d810420051628049060b0700240714036140c08100200607 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 453970584 1250 453969334 453969349
    0xb190309080904110c030a080105030609190b18010c030f060b09031e0313030b180c0f221509150f0306090201030219021c020307350703051e040302 65
    0x4580c200c40010380c603180e02d1300c1000c0300c1c082d510240c496031000207040500b03103030011521170484004a00b210003e07941d00e484141c9503180d1030039416030303000010030f858001008000c1296019103080f0001070801c101e00c1880e03003910300a2106d0300c042541e6410441ca08000d81c0038000181c82c0c404412841e1840e0400407a41d5882051300c140e400080700100b207041e030380f03041c000c82d000344650b48003a100040e264142507083d10025034a0300e004041c040300c2c0844403030000c104c1d50804c00c401440c92b00a0617507002400300051454040401c2c244c0d01001401040c1d241e4400e01c009002c0685a04c5074aa060400c2c040883d410b4a2081c1c1c1d00004407601040050100d40b116010342e544030901007080106480160064050054034104912a412442c01c99960005210500b40704000702c42d058120040400da84078424101d02030141440c4108000c48488012001300c0c1101c42080b800441c00d0918440600a4100c100203c0004100042900076001c0c01c044110f00d100d018808a40740ca80346034002120b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 453971834 1250 453970584 453970597
    0x30105060d020c0607030606120e0303060d02040b1503040209090f030d0f02041503020d0b060309030a050711030d0f18060e0405060a0b03010f03031707051b03130b19030908 76
    0x40d010014807900070614a80595281d4100501100d03243e0400440144c05800c6074081e5400040641020301d00040945c01400001582c03900030b580355131035403800d02c054444031280603031300240c4690305041d45441c0c02c00d10f00048050300589984078240781c41000200000508000d1640d0702030401102c250b00d01000b150ba003410788a80014254030003444000107402964427003544081d210f1404104c00d038040e0001e10110300d02c200200101e0f40300d041000620b010035190020380b588144135800c0040d00400060000f2402942c4140300d19a003000000e1901d03000c0c080c50307400550301c12444030038a600072004524042488480c0103005007002781c002c04e55000604010310944e181c4010070030329242c0b00405009022001041652903031541b1214202540510045000903c0c0f0704940072040c20840300f690040e4a1907036024680484002160b45804607a10300c0c6c4024001049082080038410201600900b40c0e4a0102d460759035821514804030700000f00c450500d414414030b03400041342e8404440d030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 453973084 1250 453971834 453971839
    0x10206010b0a020a0611030a0b040c301d1e030307270311100302030c03010e060a0e0f0103020108090d08013501050628031203020903060a0e060105040c0203030105 72
    0x88030750140100b203260603404c3c0c3d005001103107025001c500c8802c11000a512984484500f03014000c1c611080c001203c0c3c0714080ca100065a00c0c2080210031140040f00c000310103030002490f501000301420030100d91000c1510304440e80c0084200078010810b000c070b0300c11014442403929205018001a40d22440001c061b0320401401c13050181d902c1040c50703000402c0c000790100c8100000d49034944101ca08502c00a528821203030460400c0c3c00c2ca2182c005c07648118000044181107929140d00e00c2c440a0000d8960b96101c4d075640d00201c0c441c0c82d5448220300c1407150100d40c80d91540355000241c0003040103000c410498005000c241005c9400c030a03000d0454003c1102d459030841c03121070340c2100020b0382440c3e00c5a052020400940500c0540140c0c2c0a02400c540d06003041e90700f40100e92490350402980030191194040403c0802c0c003250384800108140d040152400300981c00103814176100f1a0101172241c0d41f012030720b4811008000c0d00b07002d08400d407401c005284500c48069640e000501c101403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 453974334 1250 453973084 453973087
    0x9070e0d02130c0f0201060f12170c0a0308060f1c0f1110050403051219030b0307120b04210c02150405060708030a0c020a020f06030a0608030415020609030405010206010b 75
    0x315150200180d0714900818010000c01605403c000e000c4150100c01400640c00c1600116101c1c180504140c12601c80310349412100300c030781ea510040e968043d40c024004a0041c00f42d184404814003112102d5440b03684ca6150a01c2d0650030030201c4d590040c82503019a086001382a1210342100015164a4001e0301030f960080e210714010301d008001d204080e401800c01568a010705401030003800640e84190290b510740740782d0000c01501400b460499529000d03500d501100b4060180e400400c09000c0030741969020354690369a031189025511048400c66002010002848941d80303002c400410f5013480e52172131081e030b00c100030800100440701a2044145043003000300c458001e81101c1c0144005044241c80f03840b2410601c181e50000c44002d09072909060074101114404181e107810720342d00810106d030f4401c041042c0442038100a0092014075035800340454903c0c0304002070401882481030847c41c0d8088014000e041230340c0600301007119070003400280b01d91ba130040303a13041c1954000040c46 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 453975584 1250 453974334 453974359
    0x41a1b0606061b100e16051207030332220e15010c060c080f07020601180b010c020a08100f140c070302030d020309070e060607030e040c0201060906080601090b09070e 73
    0x43c108001c445001070054601091244c0565011640042086c41004c0950005030740340c041c05094980d1010a1006030801c3e0001d0001902500d0600080020900b40c60030400200851100e03490b801c5140d0b2400a0000c5100c002c202d60f200c80710300d803501040e003801141e14036103512200c9549003d0007640c4665049480c40c0f116074132036001180d500b50401030511001d001d2000160550100341c0380640c903c59a080040c480d80e00010340141240c1b020350b603414032004107540c51030003040300700c40d054100685c098440d400b5070342d5824040040c12182d0f0240010300c207201d005c0c2d0308507034038a440326072500e00f80007402200c503a039480920740c000b840c0c042700740e40d91300903103012401d62042c3c1c0039071983c241c0b01000740841c0b2a4009030301402e5807880740300300300d00b501c13608100310580c0142c00f002030025109001d1011141896003203000c1c21046400045403050302d480401d01540c82a07008400250b000e0401000f4030300007401207550034401030303405510750b0420304001002562020b10f11805520380005a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 453976834 1250 453975584 453975637
    0xc030c171f0e010518010b0d050a02010f0e060a030e010501210b10030804030b0f0a14071d180610091508060f041404140d090614041a1b060606 63
    0x1692402c400e00008020618041c0c000c40c1c0041e440c118001c40541c138048022050f4102281c8024031603410100400300500300b0703401114400204003074a402c012070320350748005540b58440036080c030002c281c4011540d5150004410300311041648400070144c2e00030f501e84601c3e1401d42007540d0f2241c015410307142d140d94645400040212a07400103010300701c00034000007407124004846000d40012800d00f546030303c500c98108285d6400c8103030920707040c42a40100760000d015682c3c00c0d081c4152000a01011941c0301c00040c2011100700040080f140004108801481d00409034100154a030402039041401d04604a03044d19002c030210060004600c08981a40d98005841015040081003400100301c120549d507288030007501c040350b980c40c6d08100c0718540b000218800386e46807415550002c03485d140c01d0084a1840e80e01420150890b020400802d0801e050f025050120f01c8041c03001e50340c2c0302c10304042100c02c1c04550403032880782c1001c6c0a121a99442d01c0407a4094500e007901302c1608240c40341c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 453978084 1250 453976834 453976841
    0x6020405060301120c060f090b0c1e0a0b0c160312060b0711011206080c040c0302070204060602010b0a061112090303120a1a0306100e0c0c0601030c030c171f 69
    0x41d510000110000070b8580503002200451352041d03050b024450b680d45010b5a086031024900e40204c1c070101014040c0e90100000360910308540d904554440c6400d000e40351040300001104039003600035584500034880180c0405802500702c1080e5403503c041905001c907002480c040003010403d001195000300203807908500040d05a50310b80964500f04d030304e4105c040b184000c40071804034080302d000d800e00c100d03035126010803104001c000d085100340010400002340303500034514040c0340d0300788100340141c1c5462141801420003900009a0131070408108040a20b150748240201b001010803d8107240c070100c0d0170b2070380c0c0e00d0785881c1035112582000000d00f140a400712031009286100704002c50700d0746980003444d440b010401c1100006a039201072503103841040300d080c0e140d4a01c0c4030040050003042c50041d540f09417411030090510601c011031608001c000c6c0d0096500408146060060000800740c402c0205003000500c00b81e80002c82c81d0f2030701c641400d90301020b149075945200f04225a00e41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 453979334 1250 453978084 453978089
    0x1b080c070b04150f110a080d0603080c030d0501170307060911120607090f0f1509080d03051506180f040f02040e09010e0106050604090908040302060703020a05011521060204 76
    0x19254482c2c0d1103818503034115600d8440b200005078901003003495280524442c040302e070b40c034034054201103441da1500c16050340095683c5081540d594000008541c100001d0803a0300ea006000d145e49010602c218001d0302c106070005030203040c1000f440c018000380002110700700c81d48800d01041900203070400003010400d00c000281c000e581100802580c10012514602c42c0c180e684402e10844d031543d005040806440c043d0f40c5400802d43c41c103100041c040341c2c02c128800100d1600105240e212000642016808900c10022030b84070428041c01d403100404080d034440003502c2d40343c10806c011640e0b00b80305c08000440381c01401c2ca120100c1280c0c030fa5401104400040d060195920b641d25440000c14034011100014694039141c01c1c08148034060141c18115200103050307600301420880040300400703461b0001c49003100308010000041c0c4801019001c1c030740c06034016200e0b4110b0b9040160039070f5504210070300042c000d0402032140004102d241d10300d10f10b007400d20103680a680e1400f84001c3c401c68 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 453980584 1250 453979334 453979349
    0xf07050a290a1512060c090b090d060b040b0414070201052802030a1506020c120312010513020913091a0c04140f1c050d020c011d1c0b161b080c07 64
    0x501e032003070a0017007a41150f0300307240c504d550300901160b851120100500030b542500381c0c82441c01d101d03030021442540001480003401040000d0040340c0e900004e00302e4082c1e280c00e02c070003900c00d400c004295030280b29a030f42c04403110043c02000d1402c401204103503024600305006003540440807030624a40b540c0b080039200c203412007488009440c3e45010755194420810644102010210000115030200656044d0410306000002036401e01c0304000494038404165011258207010100150351401c203011302d071154030500020b540c441c0e0b04040c1900800b10108900000c022424028400e58060849040300c6488559110074414440010b03a555502c40b140b540c0040120b02500026203000003004802c5e2292003102c0900a4180c810781c0c0ba03581c456070b064046000c6841c1c001c4200495040c010715207000400c054404c82381c2c00f0700700d180d10051040c145c0f17641801d00e08200b1120501a090040c4408500b010f00180f0480100742215480308503006041f4040403440f2042c009040041e280070b400754 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 453981834 1250 453980584 453980609
    0x120d091118011809080702100210060b04050f030c0a210602130801140f1308120703150503030c06220b0c0705010f06061e050f07050a290a15 62
    0x6070031006440ca07000b0f004148100c0c600c00030750342e02442c01e8883d4402e02540200c00b0342c03c00d151a000c0080c02400340b0b01d0b40c010341c01680d20040052100c0d120b0500a00a4408010307115410102440b40704160080068003a62125100c89816030b240340280c0103c610421842d02d60b0a201c1034501c0fa64500548010b081d1030002c20b200c0902c14003201404252100003008010321094200d40200c80c60050740c01030500c404030000705a88007054075116001070300482c092481d00072101e0048413299411543c00740020f98402d01c000117082500c1e115401010110000c0d81003c4a00051039140d42018040000d2000d070816400415105003a4501c40303580c00506801040c40c3c40c40f6901829800040d0490b015440c2000720b9000000c0d5115100548501e41d40340d481c0c0514085c2603582040f45041000c0501806002c41e84040a540d0014440d080c46038020708855941d91070000c0c242d000740c0f5014412083c4c003240c202001052985191351000a8000115440c40f90031100404980c40350040c040209c0f9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 453983084 1250 453981834 453981859
    0x11150d0c210f1b0207092f030703090b0403030903090807060e4b0604030809060d1b0210050903040608040201120b040c03020304120207050906060a1b23120d0911 71
    0x1c001c54000d08071a0f0100003440b040800301e407c0c0c1c507a0210700e211a480a0701100383c1c4d00d4540301d800040c5510044a00300003488280c151114001c2010032031f8110700081e191102c4100701580181080c0003014440d0007000c1c85820a58027600c20981c10011038081c80310304a0780421540d89100c500c0610002d200380380b03804c6840c400e40900f180300c202c0141c0300041210320645414240902120101c9800030700c1039040441400400030f40d60700a050540c0081e0300e4500b006c0c09194202c03541007112109030014501c100340c680b503040545000400280301900f092004021240d0480c1c0315683c032950920b0f0503840385c8030103d6071000916103044070f1034020380752242c60700565070181d00843c05103020b0b0000c621103000c440403caa466a190043c030b500640c0600106603903090620140565408a0070014194410b150418401c90007030b01c8151000da5140c01c0c4552504203055500300510007940150562031240d4000381018451600000c2d040c07503644814074180000c00c4048280800000c101e0512041e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 453984334 1250 453983084 453983087
    0x1e0108160c15060501020d1d0103050402010e1008060f0d020a17120c010501030c12050a08030c0706050a020d0e0601061b080913091514011211150d0c210f1b 69
    0x80f40c01850301601c0303000341c5484810700640e1b402540b01c070761855100d0300302440f5004601809010344101c0c1031004140b179140700d030355132840d489000004030b6540303250601e80300080100c00c0c1d0b000481c550048030f8002c103240150b1070748002c60050700d46403401007800d540440341840c42c100f11441c00d800c002002085140c410181900058100c901424952014980f03420394003050a81151004010744d00c03050f00c480002d4407076406103a0040c46640000c0c28412240c5505080c0c903422900b40840c10350008a04100703020328840e0614500c0210000d01c660345c103200d0045c1104c10601d5501141c10764001030718007007003181d0080b1140080b01400c07003050301170301c2030244014011124003142d8203100c04800c46410851440390907614910101c0440c00343c0d1a282844078841110003090316101c09260202041da116410b50164101210707060301d03a40c0d21004102d40c121004845003078200a10903400e103500b41c04040103290880382907280010400280901b40c4014201000948244401a02d1a4460307a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 453985584 1250 453984334 453984341
    0x80a05210412110c0d06020c0d0206061c050a03140403060603110a060f02100b06090a0b04031106040b0316110607030e011a0a0b0a05070602181e0108160c15 69
    0xc51050030034000ca800a0300042e02c142c4101250f880072684202d04100907858010b0101015500500e80180b4214901203505d05204003041030101503482141400362504192203070740103444030400035010304102c0c0d0346e405481d044068400340401034407c0c1901804150303002220025503000500b000415a6440e000d0155400c3c400c00510a8104120008805002c1c260341412000a903015210044204800c000100710b941070490304500140b00c80195900d800d00c466000d072207885403090702c0710705e185080c003039680060072183e001d810140000c0264840c2d2100381c1e0740040220540d0100c00c03500c2103007100c14035102c0e11120000e01ca208103000015406a10180c078091600c0001d0211518544101002482c0f14020399041403100004001110701c00014143d41c0380f603450241e1a00e190b944030b2506a8204408091401c021b0800da92000c1c40e1090320719220002000c588271700d010301c840010b0048840241035080c0380e002200081d800c0c62140201040c21580030050030003944103448580001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 453986834 1250 453985584 453985591
    0x1d09070e040e0106031211070e010e0118181113090605180a0f0605100905010602011b0e0f10090b07081b0f121804020a02010506130603050604080a0521 67
    0x1031807a04440702d405000601401007601d8110802035060030301c1a4049030034000710f04070289103001d051004030381d041d8406800750090001e482c102c000355050111301c41d25000344601d8103800c189881d03440d0200e45040b400340703400755400c0640c2c0c10701110006c005c50500804031444940c080e1074080c0000400165074011801100a003443e00350840b070103100c491740c440d407840300035007031440104d01640056060382155902250074131581100507034402040c4203480007a040680035035140c40d1481d036038420b040c0246090700d104d031500744041c40754803010071a912030f0300741090f018500a00c94403082d2800f440c1c04000034191421221360f0303107806050171901a000f148280214044610031384890341400982d2402090341c04015040c0385140316203900c01588001090403030b500900a100d043c9503228806001810b00c42d40010840385494810403c01480082111840c1842c1c02000d10100d4800200681e11981c081d8400f5602c0c84400c105840d0707805207140d07800d22029081408844010800a560300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 453988084 1250 453986834 453986839
    0xf0a030909060b04030b07090e040f0b071e03150b040b040905090a021305090118050618030c10020f0906070f0c12110d0f06020f09010e0301110a1d09070e 68
    0x8054607401c6050603500540724280112409100a0001c13544c070b115540c1c0c10665500b001030006a507a007442c0d0b2007502c100c07825211107901c5440942880707848040240d001c0080e10b041e003204610407541e503001003c0ea0354482c04041da1611802c1c40b41c45060765083c00740c0089950700f41c445a80750820f158542c05170040508550901740401c6031981d000624684250740100404602d150700d000501c000e00340100001c07515900c5104402401044180d60307003d041c0500302420301440d00000401074440c031204445e00c00d5008104241803810302144520804608500160782c903000c07645080d0041c06001801540410001001c2c001c000000018087e594070420300d209a460380c03100d5840320420001c60240000e2808980da070700c186000400084003030b2040340c4c0203d0a91841d101c0d00304030f81081d52481041c400000e80380080c0d6030080c02020114030b00300c1c028071101c40145444d85060051182507414030a2041c0c1620140203891200508400042d250100350b1402040040400130301040450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 453989334 1250 453988084 453988097
    0xf030a020c030a020a0b180d0308042a0b1b03040f030c08030f0316020f06040606060905120a0809150c1005011d010e060d060207050c0109061d0904080c0f0a03 70
    0x50032030a0101c1c0780c0ca240f54000f0314000385245460750030803191b801081101d0b448a00c0001051a60740c48094100b4450f0280c4d0318614540307030519180a00c1008000b00641c0314004200344007020f0982d0300d5210a48104007201600d1300c182c821482e080040310700318140035010108010030020907800c0c0741c404076406070500d141d8160751030b900759403680b00307021042e440600308000040c095199450140f1003114988110b41c068440d4204075420404c0036541203c3c0d86403601c00c200b0099030f014030510050700c1c00710b0b00601004000d81d800d81c1d482c42e40c1000108504004111070500303640301e03000c0022200039407185a0342ca15070981002d0300c03403174a9418902010300c2e160001c40d209410540d1201001349400e0648041c0c1d003801a030007140c0c140284070380d50100a051413030001920728000b030504a4030900041c400916440d001500c072002c980c100c4001c12a85240d03064411401650f0300e100d055040d5001040c5d034031507040ca90321922940d94084030314411440f0302540c0b003000040081d0002d0080c2e5920 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 453990584 1250 453989334 453989353
    0x906180b0f010b09040c0909180b06030309011709011b08071e2313081b0405160e0f0d0503030a2904020306130603080301091112011203020a050f030a02 67
    0x41200704800c0c000d500c0c82400034010041c0508160780700a8140304141014004e1a81c1da03007610055801c4c1003074070850145e020781c01c40100710350001100d800540c01c0300910b041043c400c00003001900b0908090802250900115000c40b03001c2d480f03405010032071405d18030300444d40701e40a0b2841006682010000e00c0000c040301d01024034800540950300c150303a401e041c074200801c0102d0100c1440d0701c944181e000800c40c10304520080c81c10307000208030171b8015042e0600c510303142e00d0825881180c4240954240410044100380d01c070186c2c98000001e052070b15103140142e000c18002c8082e151040d0b0401d051001c4a42440790000c099442007035018824448030500c08480c2c01042000089030b00e1001c5034101c00d20305468242c003d10340c400300207042d0440032507036004100b09452443d40141d03440f001c000700600080d4014000c00c0c0d0255180403c41d45000030598034880a0501445404104040f950402080600c20710101110310f81182c111501d03465803020700d42d107035400740d1207400c0507220301540c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 453991834 1250 453990584 453990601
    0xf0702090411091305070e16083105010b04111605010e03031009050601020f10020f0f040e09060c13060305040302010b09011509050a030b13020102150f0a05010902070b0411040906180b 81
    0x4988c07203040d8030b136480c43c00c0c010f039018141c60811000c1c1409500c0c12112140480718004005d0a582e8000c0d0423111814810103800e1250854200c80d02c8103002d41c0c1091031440880c550302c0f044550407078400c40303104410340c03072800c2060040c0341480103613045020000901c020a020003001c10142d500720607003040a5117450b0016aa90144c40c0b18042031600100e0002068820716400303000c0c803010f0340c09020714003207401ca078205180e4000d070030000426081505100140350100701780d5600c5001a6402403500030481d10704140b4841c036100e19130405895100040400d03100390000300310110301074903455007940c40c0d4060306410020104044009400050001410b00d804541c10080383e03088a8151a29160380034865410103e50ba0181e045d841514010000c04090050039441108502d2480c80c0f1030910148040070b60318103070310100c0b5031801446010042a10700c0040c03a00250f11040001c0c0118445003c03901400c03d020002d0f00c6913142c01c005030b210000c803540d14500d403885804e03800686c2c0e07200c410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 453993084 1250 453991834 453991859
    0xd0507020109050a0b060d05030418050108030f07061a120a15090308010e1302190e100503030a1d2d03070305071503090b13050705060f070209041109130507 69
    0x5041c0d40e20484403440899650545170760040409400c00d4181d006035240c952950303100b41c0c024502c4030030201661020004038800ca6000d0700da4070001d54600340030f82c2c1010202c0d024110b00a0003e5680f54148103075040c0d04000c079249540060401c11501032680d02480e00e030350034403000b46da000101001d211800c1245100e442e08259142c0c6940c2e08507401c5c108558108403009020092090b88145440056652004490350002c0304180050486051000e02b940300c080c041d14101d00ca030740d48002403015603400b100340e46514900b494030460005469220416100300d006207150451056001403100300740b4420340d4441810b50131a204040c02104090646d200d0719440060003641026005002c041e00100301d080c5e070400c80d0325010403d403815440b071120404042c1c4001c03145150743d40240d0104101440014001d16048407064213000d080904504075114440f0003d1040d80b107c0300003010001080303506c00402402825005083c136000324206504e41c5020415140ba20800100041030012541e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 453994334 1250 453993084 453993101
    0xb0a0b1e01080a201602030a0c031e03200718060311060f07030c062a0e12060115140a05030105011106040c090207030c14074103100f020d05070201 65
    0x81200c4e040010407030454070390000220f401070041c012044402594040048a00b4140550314940d140303861898064103000036010f500d640d1449006201e00402e402650111031140c423101c81070384458004070003504090181e0040000302d04c5e002500d01c0c0c0d03640d140e40305806803881103032020a80c880f103a00b0807125000306550900035110170014100001e12450000179020b21441005c0740040584101c40501000200000c4170110300440c4441901d911003101c0c84551010307a503801c1403801e0515000e0716102d05005140785024010078034010144218401c03c5c4802d1074450090b00c403420300f03200910321b902c284603050009413500100e540d000d00c0410360900569100c20f091403500d00d8000c00101039000076030180c090180403420355000c50402182009280b00d6400500301c035508081103440c0398005143ca58418445014044641c600c4500901c880d003403070110b550000c811081e00091400b4074464807a48034038100000049004142d4024190011056106200c0d43c0c3c0c89107800c03401c817002c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 453995584 1250 453994334 453994361
    0x1f020c0105131715040506040303050a09020a05010f021504120f1b0b0a0e1006080d0c0b041707080d06080d0503090a031d0307030803090601050d0f0b0a0b1e01080a 72
    0x2808209003c0d40c8040c1c00c0081600500365806100da20150a52200003103809640a0b0881e50800c01007603414440c0d2940002590400c02180c621900801d443d41d5040c06194140000302c80d040741441e000b04001038012075450300740405450603142ca03000e0031020b480341c1c41c0401c06a4a004101a00820340c030b0399142c080c103a00c0c60030700116444a60082c2c0c0064880041a50b580c040d5000040c0e050180c1d071007496803100e02286c0300741703007503452480d140d5645203003800c000c0100c88060010300c04543c03c9402c07035005508902c903444108100d092a01c60f054008203070901c0026811981142034011038121625036059901c186c00c14001a2002d01c8101c550610039040210344600103801020414049214440e0403001d124103680400c2c41c00ca502d410940742e1010101c100500c4030f80811100307015000688680c03070700e00010780d200c03011150f10110007000c4940c0d590000300c1402203940f013264400700041c0f9503003920104100101114000780d1040d80000c0c1d01e0b400140c0a89018012101c107900346 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 453996834 1250 453995584 453995617
    0x60a0302010507171e0a1403160815030105070c0b070f05040e040f02060409020405040b1806060d090b0114040e0705010509150c10020405210d050d09021f020c0105 72
    0x169078284201200a5404440420501104080c0c2c843c6045e403880a000c00c0c0d11307403692840b90b00c41c043c080c030340b1025010011403410010820840b15038500703820900f01508280600f529202d00c005094ac841d0b88446806610f8001000003141d4440c10754000d85010310307005061616001d03800c46c2c44100202c1d070280446e40c10001000701d11001d401290740603010700f5074090103481550024141d640298020004150007160138805442c10744210040c4a80440c1c42c0d082200710414000801034000b8070503442900c012600600d1104d503500f0009103503510410181c1c00f9a141e80044180b5510b021180d405640380000754030b0314100000d5501c00f85c1d00c050f110542010320940030012004001c407140c01050b00d040c414403041c650b040040500d03103000d105000d030f126401c01040c000f0f0142142c8034080d0f0310414440240c9101808190101c00d40d03000c1c40d0031955291881e2004011340b50040c2d000350404c60b01020040444048140f00110303c1151f400da40750403240c20011907031402245a18a01c0700304 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 453998084 1250 453996834 453996847
    0xc03060105010806010c06050a291507020d120201022a060103021504080105190e0a0f02061315030b030105090f0c04050a110412020102070609030f060902060c010c05040e060a03020105 81
    0x10f140040e03010b035052500040d07200d03d40c1d43e51001c0d1002501d00682c900d48408260300b04100c0c66000c65900994043e5800c500b045030000181c942d95001b04004298030b001803c0810340d101d010f0700c8410160030051814000582c080f00a000f507005200070f02c2001c90001041070101c80e01a03104203048034040040a43e642035400700207403880d40e44003403140c941080000048209003800740a100b0000d03004d110046080c2d5102c40c0080d6244a0403d007000c0e0008011880015880340d5408000c0703406807016a2201c0d1031169072810000140c00014803050380c042e05098403075042d0001c0e00000001e0f0b00030f1020792101482d85039145100c52190605070010b02030040c180c1481d50045601020000004c58820711601d0a100d81d54820f804c81c01c07803080d0700b4550005550301081040c0c010701c032503e49125081e256403501800c840c1c80c540000d05194a501040044d55038841c10340d403440328400d008115002100c84040c2140e0711620520000e0301102d00080c03064500003850600b180d8068450794900300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 453999334 1250 453998084 453998087
    0x30c071404021810260f09120a080903091c1b05060a1101090b0106020706030507091a07060608030417060a020f0a20060412020c0f0109051002071a07140c0306010501 73
    0x2120fa82c030600c200400759400103920391740d002e03181074030b0280c0703210300314103801c140c40742ea22000b00c018001e400342c2c3d00c83d04900000c013040f8002c582d0440c5e403514150003191070310b2039824158401c28204c81d510a80c80801300400c0d01c080c0c100e5100d498400e60b24200c0e19848610b4080071044103201d0942c1c00041841107a41311070007028402c07041c1e00340d0340000400304400c2d5039451205000780c0004c030041c1c0c852201403110942512900341c2000b0039007441c02d02c0d2481d028907601005d901c0034003005034210105050042050030b40205c009826404282d84d11103440e4032100b21442c40300d03000c1148503c588004038010355100e20071910f88407c558606807400c050402c05031400c400510754201d0700c000380d52410a244c0428800d03640101d12550001350344542040c6e00071703c1c003000c4040540c429141c00388070614680e00401c1e0742044aa003541c9000043c4ca400400b6400d190041c0d0048500c00542a6182510310400b0020810140325250340030030011030a030010342e2440c0700100305805134000c2e0b0060081d903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 454000584 1250 453999334 453999349
    0x203061e062b0212011805040f1707170c12040302090609040203070e0a140a151a0d060b1905030408030f1503010219030e121207020a05030c0714040218 67
    0x4510840c80c20550b80c24030418040b030303000c116031003803c03e070700c03001071000851526140c4a080c0d400d8a0501207420551960030403402c000b00000c00111f0304103000001c03d03c1034401c1c0c1b9541a040041d981e01600c41c0c01600c01d440d4400748480341640074510740c05024850030b80554090700c1d0060310201d41591003100f80310400c2809401680d1600c40c4207030009005c0d11304243d4900c508080c403004501d96541503094444214081c1651301c1860a082030031903800312104181d0122480340c025400c9928410751101014071508540c008aa03090400c0885c2c800580001810781d0380380184c41d6410218400c1d02202c6a0000380c80040c44c49404001017001900b1518400350400080100d2415140110340000d0072a44034400a40e80300340b034202d05c00401500340c03003078801c10754120002d004c1d00d0144156450280c89804e6604c0071300d200f81008030700c1c1e41d8070800c8180d10b41940041125501c1c84406a80343c2e442d2514464101c8054032480c0e92904e03402e190096070700c02d2202c0d98003c448803500700c0400829 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 454001834 1250 454000584 454000627
    0xe03040b0901030b060c0d14250615060c050f010519020c070f1e0603020c0a020613080d0804120216170c040501090c030e0a03020a0311120406030203061e06 69
    0x40607152144609a0b0717031084001c00c1035810b01c82c010210700b400510050401c921089841d516a6014020006600282c0b03940d11701c8281d81c09860140c0c401c0a14140000300f041402800c880036090b0004034203150071164002070300e80148210703450180380c07000c018281e40040350103000b00c00243c450504c2061860b0090247c1103a8002600c0680344c5a00d105c001d01203203507200c40c09960900c2d5030240c4843d000003034000640698a070552500b4144220f26a03039a00c0c159000340500000960141c00d8245501e000014180d28025503c51400b8201c00400110040e50143c92035002800d01d4135030140000742030005644080302004015191051384403c29040b0b40c2051030a008420700301c4081d81d903600c600c40c040d240900000035403100d0103400500f114071b0004802c020781d010701024000300b03800080381118a41e00d844c042c1d50550304510600c0c1054120800034a802d4808075010544a82680103140308410a80710141007181100c0d04008c212a404503694001a042200a06134030a80303c01150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 454003084 1250 454001834 454001837
    0x10809071a07032705011d0102030f0f040b0a0c031808061308090924040203010b040504230703090209060f010f050306030c12010c080105011106060438030d02010e03040b0901 77
    0x3107042d981140c0341100000c4c00e003100715070204070b441130040390b80203007072000301c0000d0100300030186143d0320001c1d41d24800c0880d4000542d401003515040328180384102d0703014201e0324210f6078544590850160485070508070480125511824041d4490307195400b00084400d2440200b42175114840c4800e0070300d00344a010349000404100a030b8885d11201c41c2140140350301100c0300b464101440b40502c0a0b01050381d414411401003004124001000c02540c06980080302e000402a4092450102d41c038440b003030351542c048130b02e001c00100641660103446102e00980c3c0d80710442e50b0f10b0040103122541c415015011403200380d40800d030b840c031a0001e198051000703412180d9101030100060702c600c05401032040c40d40e441d4180340130800c0e030200c08140182000c2c01c01070343c411641d040d059281c000041925014039070ba05500c64000040004a00440044440b000c0b0104140846e000c140c030700ea1180d0030f0103032244843c0b101c00d0754414440c035021415044051401e00d828070f9050561607201040403030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 454004334 1250 454003084 454003097
    0x1b080c090a0905160f0e0303190201090209010303030506040c08041218052e03021317210c1c0e0d11041b1805150304031404080309010809071a0703 65
    0x2d5040880d100b410f006403400300c0c01c1d02512508200013014001c011490008020148800c032500d41c03000400d6448100b190100e64500d50300020080f0300404039604007952003a0018000014135805a011303600644098801703102c150410b03a000e0790410010f039001405a41c88410450b0807500c90f142084d40e5641c070f503920001da02c0e5a600014020700040e0604040d02d0300000d42c04a0101e824030303003520451082c0c11b0640c140001da8170750300c98111262242c04422106007440c0d0751003480a00c80a138600100c0c688184245445000b60011a00900042400b6101d8a00c160415030820010700c0070b40c0010380d4861320b08100c42e40a001d07080303904120880d824547c407c004a41c0b962680100f0080100648002c5034090100e07800038a145546e0240c41c007003411a000074403182d16a5560a4a450002810559607407501d107821585070001c18249901d0140210740820101c001200a150005d000d9807404040d44540c0081911038000e48586071600003504900011402844080c1940c280242000da = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 454005584 1250 454004334 454004339
    0x1050301090e0726060a06080a0b07111605030f15010b070303021612090b070804060e031905010608010b060313390612021201060e040914030301091b080c090a 70
    0x1d0080944948502c4c2c0910036079108410342d22005c02c1500c2d401407844500f840741702c3c50308101c81e440e05056240689800219030002c0d084500400e5500c400c2244001100e41030181008159203440113401070f584240201e040007251440009001c4a40e40b0300e003110852103902e0308243c5040d980c0002401c070300b4503030207202c240d40d8003502800728990f02d4000d480b0507400440404c0d004080c0c40071a040118014000d02606010520b601c00307540c103880c01814020280a00d180010b8605901c1010380b200e05981104548100300041d00700d0800c48903410002d02019410305c08005243c001103c2462018403444940408501e0008400420825110010310883d1034140c1905100769501004078140b04001c404001c85c6501200304071040388115070450500000c0c41c44010003440620883c020006a42c000c00007070f5490798000d1025650010140c3e80c410780c0103030050303103070f0301300348a0781c1e40c5140780090302824000180c00700c0c40301231107995466140c0c3c2d4402d500c00f840c9170041c03410541c0100800101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 454006834 1250 454005584 454005599
    0x506011202180d2108160e041d15010501020304180b190e041707020303070b06010e031e07080f030f07060f0c030b040b030d020d0806150313050106050105070201050301090e07 77
    0x10740743c005018a100510a41c0c10003e02626502e40540740010064048104a2181400c941c1040070141d94900404030300030756000540905580c1d40702d45881c00310014642c0294000090f84012400c081072a06142c0c1c0c0c0c2c9400580c2c44e800380b8407032508040b0b082004034a0140c21a80400d1880700000c0c500044508641c00d2088841c1d415000121102003610a200c18000864503e03030140720b00340c2c042460314243c2e0340800e46901518400811049840000c5441c6030b0160380707400e043c40d00140454040310b06001e04880b050002c0d0441000c2070044e4100420480c40100701c1c105803c1513180114603108100e11b4014865000d03a0094407050740c0d45120000c010785a004040640c00c243d030300440c40b92101c0040000f2074003030b5030312144030307034421001880610f4010404e207404000303900b40110300b80c1d0350300b01048860490901c20781d81c0c0702c000410040c00c00042c4080314182c9005070001c03c141c83e1a5001500c0c2d40c4504507002e8003082c420300041041c0841608090540c40b42c10080c3c801d10780d5a02e80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 454008084 1250 454006834 454006849
    0x6120f071206060918051c0512060315241807200706030207060b01080f060f03030702090709150503040b060603091c1d090103020a030204050c04150c0c060201050601120218 76
    0x820400c05410320505c81440003c12403070741d2144031400541040028018007030698403030f51040b141c030082400300080d43c0d035501780300c440f0021a810300f1104031454010003207101d010404048004401401a25206a040a4010380ca07125015040301c4041d464409003600c410002c941da030f0703401a46050960004140601c4a81d00801241c0c401686548040c6014030550300170500b03036810040380008214074400c00d0a8401c0d00b0000995448940354024000700f401c5100d1071402a40103004002400011580800054101e540c00e0034601d10003010345204403071070f00c4152009480941d528001c0369051500d00015a044000f00c401c544000d408103000d920300035060300002c4040f60f00f141000c04e4104844c111414003100440d1000250341c115400500d0007070303181c08041e0080e40d50760002448034010300c0c2220302400c652020160720f0502d000004100c02460b10080316500122000001c83d5801405140e0145a05031035800c60314036202100d60007904028070030f07007800f0414004181161202030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 454009334 1250 454008084 454008101
    0xb060d0b1c0b0a320c040306140708010510120b06220602011a0a2c0a0204060e0418030e01120e0307020a0609031e0c0314030306120f0712060609 64
    0x30140b11903203402c0b0750300c50446200a8a4000c1210100b4588800d2440303140e40c82e1140d054102d140c801d54440c90905142c1d80250741005055614000c0d8460096914101e1244111040d80e501c07401aa02c500900010b52a0088a400450300803000740003180c0d59600220b042e800060441414001c50300c40c00c0800c60010718501d0066580002c00344420703642802146012608003401c03042c46800c2101081507503825110300c81003c41148112a1203203052000c50308032945d600390841c00c0781000313180d0400070350180c40b40f940824041c2d13503480f5850038103001d000c86103c2d100d00302e20950f0780c285c0c500b40d030000c28640d1124100000000001c1c83d110b42d51090b44014500e4200858403458107105001107055950000024420540310400005032404040c0f04121403040c80e00400d54514074180a2a02c15500700920005841042290f0b100c1b000001d03520070001250a0750540514000503a120400305418031180d40048009000d0040a181c680f10010301c1820000798055640a21408462900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 454010584 1250 454009334 454009343
    0x14070f210b042909030d0e0106080114070e0d020d020111010b0301020c0d17010e060105070303060b0f0315040e07090c020c0306070806010807030501141c1211010f0b060d0b1c 77
    0xc268812103400c8542042003da503002c1c442c2e03480b81c207080c07034250303520f00410b10440341d07041c2c8492041c024404203421410042c80340e04000d01081969200d2004524000c4a2240000c0c01d10301031143c0510300800262145070300034007015104a903d400448940340b0780c40310700d0070301c0d0340366245500181ca00748010711555000c58040c21904011090050254a0902d1801e204411101c01071280c8020054210380040007424103a0399100c581c54183c01402c91540a84a010008104d1841011092008601c202210660000903a00c1030040100b01e554105035000039600c14101406143c0040e4422412494140115501d010101c00003d280080860b1f1520004060700180507065801652054020006050a210310340c100b10141502d2440c540e40e15100c0c884501885a0303a00c40e004003040101d03000443d0060450b034941000c0d10131905500d07500015841d00490703621003c22889210510640100051b1808007a41c0d814009081903800041d406a01c004c03160045140090386280198400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 454011834 1250 454010584 454010603
    0x70312181a1809090d0f05090603010909050a0f080414040c0206040308133c03020a02150705160f12020f0402070503130e064b0a1214070f210b04 64
    0x854801000c012425112006000048c8038100b101d9440c14150317410341e4816030001a0060b0305092503441c060741e040024065032040481e40b0103000c20800100244d6414a82ea00b14005403601800200ca1455446d0b000680080c0c0100340043e00c540c1c20b1070342024481e0307402041c1c0b606644400340303410342100c2984104513001c500e00344100b038014030032001004060b09800700d0300304e0b40d10080d440311740d071b104020b00c40c071241c46e048101c0d8040e00c420b81d610107400c08120750360085103001c0341301010150300490107600c1d41d041c40040c005510008400c1d82c0c42d40078004c2043d02c110801800003a410101d401c0301c07140420300080440c0980b03118800c004148040d060035142c00c015082c03124217208100008072445e9416a511420300310040701c100c2d01e030780702c500708460810003140305030360f500e86405d56541c4401400c0780043c8000f1141c44024116001d81c040228952001d4a5070ba9548201c0c4540c0c518040410070410104071454018440c0c180b02c100c941e2400041c1d9900c034989803c08650071500041d5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 454013084 1250 454011834 454011853
    0x1020d02210c0706020304080f040306050402030f01051014060f0307051b010b060405130e0105130c0f0e0402010518030312010311041a0d05010e070312181a180909 72
    0x3070301070061448154080c1100c0c01c50a204996198500c50b0349005400030741c0001c003040400c01080102d400310000800101c1c0c581d07407645004400341c64141e41c00c0e84070f8415400101c41005041c803e0900889810f840803a455141504c0d8544450710041d45a5001c0b500740202212400d02a00461103400240c1e240d613603400600410003984d61220741341c12840d03071400181c50040e40ba0700085900790340c1e00b1104038000c0e02e51100c03203202070240720396403e919500745000e00802c940d11074580c14140d4801e01060100304c0c1c5030014a803003d51948943c0c410f21886202084c0503500540040814150b520189400704a0340360109203542d1000d000c8048108064004006002500814207d040c100315414884903032a0094680c800c18441036152241d1084851641004001d5104404c2034900f02c09542a0790350300c1c10041c0080c0c030303802c10707580205039504002041d09550034109400d0f01d0030414400002c21207000f004005030410000308615042d0411001000c0d6034465905100f1107000c00145802407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 454014334 1250 454013084 454013107
    0x51c0e0f0d0509120f0714090705210a0e0109080a0e0f030d0c150204061d041a1309060e0a0210090609182706180c15200f010c0503091c02070801020d02 67
    0x80c40100510108201406914400d0746401d2f04922200c0400c20151090b45450b201301004102c0d0b02241e910540c1381100040401078410080c1004003880d840302ca01e05c2c0300860a1040c0c8032060500280d05400caa0008800d5602501200781b180d0301941d100f100054280501c87c00702d0380180c00c9900840c1504104012240c800c802d0b19a1042040d103050110152140304e07030300c0e40b02c403041c441480384040c9414203400c650503a02100c29540c00c00020b00c40c40d454200e0594403038824502c244e008650600350b92440c135002e07074440000c5403c07a555039040c00345080c1d002a00844a54900702c0d103662561102c8203c0200740301060f0306035071000c05035011128145054011519008400b5000001c85000c3c080842c4403918280100e8113101c12445564210784400c03518200ca100c010f0801610616202c19222800900c100100710450000c112003484600d050310940400c9510707207450762040016843c844003000a182c81c070641c9004550045444066443c00d9030081d0015641c0c032907010504c0c801c40c0c3d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 454015584 1250 454014334 454014349
    0x6021c090c0f060806040506190b0409050603010606050403080c0321060102070f1a160501060b0c0622020f0f090c0c06062e051c0e0f0d0509120f0714 66
    0x2d08026141d9008249460400f034400003000b00014030480d507820000c0c87c0707a10398002c42404013000300c003510901c944518040b0102d4106001e00000b551916000600a0505100307010a54001d41c0b151420b047ca95681c0270000d030f0001d044104d141c0014408070040b0441811000c0000d804011a0919480c100f400286000c3c03882d4002c0036000ea0100c400c0040c08594102038903001c10407404a07035211201c1441000d841c0410a000340a9840c1020005403e501000500300340350130101a41d18030b8403040c1301d5440607158141d1800610b2402d080c8140140361407010319440b010090710b004072068114001800603041102e45007245000007510f841c0c08001480701c00e511210848841880000c20a24039008a222200e00c00c005401e03500c9800403036004500395040350000d0001c0010180b500b019081c09009090b84181c0188181080e880c841d0002285041c0640c07800d6a4042c1403c00c00350812408079200610241e90740a031024a441141051000780301a082c912070041054403080180300e0b00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 454016834 1250 454015584 454015589
    0x801080115380409151e06031a18070306060215010b03041b1d0601030c17061c080c0f07181a060c0703150603020d0602030406021c090c 60
    0x101c08000052144201c03800c80a00c02004503000154410032004811549440500c03000070550004900011040e24031740004210292401d414071500343d076055000e0462400003003000f0000c006200078042d480c840d0f403008411032411041c0c844684810302c04075441150861040001e501d022003001003094144c0a644002c000c50310050890040800003112142d806014204c080380c00000468288418561071550400c0d03000f03009201c6c96030f91001004c8039080500c000c103000807600e00080b4658041d01c540d280b0b406807500c414180d0100c0c010680c1703010400516141d0321407508510f0310102d15800341030841c03680c0314500132580c900e901e0701107602c1c100141c1e0b0004015404000244085500994402a0045c0c003010125901986800c2c0c242c2d440401ca25080e0085004903040005040006441003143e01510400d01140225003420098070341c00c0c0800b94015855196680000d0103503402940d100e405103100600b03211001151500340c3d100c4002c4000280c0d00c3d00031907001d002915042c2e500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 454018084 1250 454016834 454016861
    0xc070603060f1d1003050619060b090d0210140703050306040b060403030f030f2a0806030f1207020d06060b19031505010e0f040f060e010b0702031903110d08010801 72
    0xe54520300f070b00c590001c07405403100402000640003c15090780c1c0da40500400340d0f500c6800e03104507113800d00005c9003520746003e00364071207400e100c00054641100e00444001000181c8604070000789502405290244040b00404001902171062260070040000e000101d201c0c2c1c0e074103583c4e0b041540c1040156038004003840c1c402c1c0e07070410041000075040303900b0310102c2502d1300703010810010344168000100078695030702170b8a0300d1070701d004a6880e10101d034150041160391103070300b00344d103501c0d081c0b6a88515100311070407150f2001000c200201e0035100949003661008045541607006543c442d02520040e070b10004001c400480c0300e1940d2100d411030b89031140002d00c0d08220101007010380c0003207a0a14412181030201d0460100c103140ca0340e840ea00c01089020348240f140c0c100486014000700703284d218895440034044004249400c0c0c0408035020290002c008022094508589400d40702c00d000703040f0107000c40d40c001690b01180a00c40302c14510742903140c100740d40d0f1400d1092400d49040503403085 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 454019334 1250 454018084 454018109
    0x301060f1d0a1a0403120e030f0105090c120f0d03020702130506180402030c1002070501020c010c08040605160f050312250509041e0501211203020f09060c07060306 72
    0x2150340b20389118208a69280d0181c0007841d030610b440004a20031500054a41080148221503031600b1600508004205508503082d0240c51842079003240c0003a950803c0c203402c6400c07202d6541c50800405400d0148000640b01c2901d00c0b0724100f40383c002a01c1110001c03039000328102d8158034143d400240b201030780385010b20461410000055581010740941080580454003040a640b81040480170280f8040c10b0203283c6022204040d44d501c4c07d501c241401407041c0c880783c1856502c01e0080100c1503078031001090400c1e0400009031965040304100d1513481520304241c0340410302c200d04010701c0d00c0c082c90140d69205520300110f01c45140087c81d47c9921000782c52400d090b1420035000d2503d445203481c000d51603514150009028040340408507041c00318034068901c5420465101311304072840010b0310700311850790f03825111030a400e03188082e05112442401c06811800f940042c4001c14042c842149408440c5000941c1508030321b0f140d554a03441058180b0200d9018411a009400c8100010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 454020584 1250 454019334 454019387
    0x1e1015170d020316060e0307061b02010b030a020904060e03030406020c0c1005191b1a070c0b0a1509050c13050a0f1206110a020a030f08010f0e06030f030301060f 71
    0x2c2e550340b04882500070700e041c0d1151650140001030b480500d440c0b1340c074802c0c0c1e40d9800caa81001d501500f00c1c000141500c2d0032009040e09410f00510031900c03002d5019001e00032982d61038081100d003907030051042d07910649803642402725071806c1c402036205604c140b070b0060f1030703080c0080c079145020b1003010118040c1d1550400c1ca100070f82c00c0341c01d654100800460b802460300c070300c44080358000c01c0300c1c0790132804a60044803003081060010024130440004c0302e030902c180e039840034200c84070032200102400714a0031401080c20100c1e60741100c2404600354040c0f51501d5a50782141c0100d820032282a4212000450441052206101140001d0008843c003010b524240050903039650141d102e05503076a25001c401404000343c0e500030004261540c00c21548842c0c0b42d880c0651124042c80e422000200003821040540f4042c0c403199040e2103010402e545968200b00105100c1c4401604030b40e45442000a4140c0c900810030046020b081d807070303a82e000885140180a40602081001c0491520415021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 454021834 1250 454020584 454020587
    0x8100509010e0604050403030b040c031e0b0607230a030e03010516090b0a110a0c0f061701050607050f0d180806010e070c08040b0408010603030e0904051e1015170d 72
    0xb81d000707030045800003150b44a5145c150b0041000c0501c0980090401134001d007030301e415610181000c1d82c154030911185d180d010144044405c8135070b1155000c14207011000104101401c1190741e81c0240900c0d10b000550a0306551800c1040c1341c04800003001d40d140b035a501c1c1400c0c0207039900410020244403002141000283c4442d800e0300502925000115281404521500c0740c03e244245550586684110f80e080001e10a001070140801200300840001801072049030045502000a4007030640b40e401c00040042c00c1e88100340a0315540f1034090715030007150080c8524150600e030b80d26900c8100401d0060b03801d0f10840da61140c541a04200c00401089c00180e00407a4800700d2403418030301c9583c481c5400c40e010b02940e0040708c1a0b038808a400b240400c8154494001d8074000d458414041c50404108452700c0404c5074010500d4000014000d4034813000130008940601000c15101c602c8460480300003142e05094000316a0180d82c44100401d4400504540c8144104001b0f402c06220740c900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 454023084 1250 454021834 454021859
    0x1a0904060b010c080301090621030c110609040f05060a05031204140102030c0f0304091803170613020c06011e051011070b03010605030403092c04060b0607030810050901 74
    0x60103440d00c88801c24101d80c07041d45402e400560100c009501e80d43c6540301c0f81c004000c6c0d030041a80300d4040a0880540c00107010030600c00580c10b54443d5509a1940e4501c000559a000d0664201301e09104940030707a6220f014108001e2030164000a0900d443c0d01000a0140c40c0d910003030094200c0016140740003642c0d4122401c2d11640290340141c1c03201d6400407465031040d207102004d03500400800c1c04005202200510859203510340900880741c081c0300050300c4807008040140410301309042c0d0b03005400c0c2c220300a07511550081007100461840300a02c0143ea000b001141001d411100c0188101740200ca5800d14603810341d100e100d102c42c00c0002191481c1c0445200c0c00c00c2c41041d00602618100030080000900110b0024507142c2d40d650901600c41d400031340301140440c0003020045904006c0c42c0e00c00308899015a000b03808080da8041041000c40c0150060b02c56540b5480000015150036004284051003983c0f01c0726103152640c2c0368070741c82040d600818859000744004000103c1c80c0203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 454024334 1250 454023084 454023091
    0x90d0306060f0c080711030f0d09270c3612080f0705010e0109212102071403032a07030504050906040b090c040501030c0806060717040e010b0d1a09 65
    0x13a0b86070343e1502e60070140d01013000152010342c18468401c45031416100841d04009900494841980182c0c0700d0f100c05420300000c000d10380c1d041a8040a41c00c016020707030002035950941e4144080c0020040c50603400b211080e449441803d4a5004402c00c408070702c0c90640d0003040c060304903404012207507449040b10b00c50b42c100044003420104191003800401c0d031050312100c501e80000c1090f0700940c501401c0024450010314842c040035840a50224007400b0307100c46030301c5c5d00c94440900c0c40e004100e610081d0002c04040e0b4001d9980f04617510130f09410002140140d0714031001b022101d01070b21000700c07445446e0020300c072004018042d80c400070f504078054400380d0f9022611680150348a20205006001d400c440c140c0c0084403030b05000346014040000c0003552400c1ea000e00070341400080980c1d5200007039a40030f030840301c1001898049807220481c03040b84a41030754100e02c1d096546082208400303080e005103110300000100020124854826500d04c156249880c0030320510031b2000450061006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 454025584 1250 454024334 454024343
    0x150103110d05072c01050111070510020c0d0c1a0406020a0305090112091101030c050c15070c1b080705040501031211071205030903150609070c0305090603090d0306060f0c 75
    0x40c040381c800c000d000e00140c000340407020342c0101e0300d4256031400c1c2c80c112009490144026240400428294030501c8410b8400300304c080104071040c070303000a0028401c4c000c00d20f201103000700f0350908260f0303807410850607090303005490301d039429802c100c290940381700c04c51002c9110200812041040e00e4010400005054060174003903200c0203501d00507907100c1c1e844902c149000e0714005a4204001c0406094043c41740c082c1e07400c12034610303468016100e070310644134560b56551140e41c5c070040d028081c008941c1e20090510307280902038003981d24031440152108151a4921040c141444092070410440700103000850341440254910384810325031030000500d0008200d00c5410700321401d1010040c0b50000c140240050340c45844c03070b0500c161a03411880016100340070342c8401401021508031841c0c00317558000c20031f100c244c42d52801a01c174014040340072014400244901a0a907030380350081c1d44503500050180c5283c1505500060860341203070064000e01003400320310b100d1140d000d4603643c0e201e07911 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 454026834 1250 454025584 454025599
    0xc0d1203020307022d070501092114062406040f0603051308180f04020403030e190312050a0f1e1d040906020913060503060403030f140c040815010311 66
    0x410340101d041200c08061300516545c8040071001051501104400321484142520042c40d04c0d8030045035026621b20982d0401d0101030200e080217520383c0103031102c0c10300c9225506403514014848a041c81c0c0e08482145020889810384403501c521200c6c0340b8000a4103c420700d1815047c114140b04803541070060f8020166030300000b8004d2044128081e483c550041d451030746135951a10356160558401610900428901d40c1411443c1414000e031307015694036880c3c005048801c80d051005c145112003100d10301458620001000c01c440034080c4500610941d0382a50315151940c014004200e070007100f00801070445040403149030021408800c0d007445142800c0c07102c001c0c0c15140e00c03650001c45243d51041c80e00400740c2c100031b960750091802003002d0b0354085052609100c024100c0303c40b88115605034100b0400180004d00c681e1150502440e100030009030385800044070050301d182259807004984000038144860b01081000344000b5080c1c40c003801e255030441e680c01007000069031520b4010f812 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 454028084 1250 454026834 454026841
    0xb091309050c09010305100b040204050d0809061b0616020c030c12030c0f0c0301140c030402011b050d0309110a080319111f06051e0909010b060d0b030c0d12030203 72
    0x8144401d01c103900b4020310200c059612820402d494010342c05240032906e2030b01c6145861418a402941d045820003052a0401c6040340c0750788405078010003085074806000c00640d001140210341d005220f01d9958018002403400d105c5240720380c10b030701c1c007810155809048201d039203950001d03d48007161020345040201420313000d80c66103075004131000c00925000c0c40030340c42c4124000203142e01a54000b01d009110201503485061038901080c1d03500c0090b0030f010800180503500450300c00d0407480700034421180300c05031529140d0405900e00920000a6101d2114200b40480c50085002e0f01c17508503002c44425140940440d0360344240c00264051000b000380c6005000e020380b0600b840007001d00140c61650040c5d1800c500103822030001450140e2a2507404200ea00300001da08180f0502182c1140000412204000704c041c0c000302200c0f4107640380c0c4420341e5181c031041c0260520088050000c540c0260480406090446801c0100d00580f060f41c460380c0450480301030700088052034100140d4989 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 454029334 1250 454028084 454028093
    0x20c010306050919021c0516030606080112081201060503040606050405060319020307030501050c030106110102032e09020a18080d0507081303050732030706120b0d050a0c0b091309 79
    0x40300c903145146c054040440d8001c680310740080f0711030203161078130300940d10038608168100c8241d400759000281005005100600405858a815501804a0300d082c00070030001b80785c00803401d800c580c002a0340802804100103150150710041c0400721010b002c039292a00101b580c48141d03070007000c40c1e40c1000e003000095482c1880840d003d5508800240728500d0104400d082c1070b8002c0c131410740051003402103c601e009062003607a02034001f205110b07000300d0841d4114400710107101103000c00ca40144400080380740c414802040e00f1003031622402241201c0000e11600080d80358440e203910380040c40030301d8141f50302001311183e1035441201c04e0f80300c16404559400c141c245410040a0b44140140030545184454640c0c0810300649190078200701c5900d071440d006035600b010680c140e40f000400707200ca203010701c460a40d0034000030740009818203a140060090719aa074003d0b10190480c480041c280300f2184220380c043c0c2317442c11802d8681500c00001c502c036072542c00a241119907a90003110300b0007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 454030584 1250 454029334 454029337
    0x1b021216020f06041214061006050c0f010e061e0405060423010f1a030c090a0c05090a090e0111160609020a090c0e1e0105030f0a09170a020c01030605091902 69
    0x182c005040540c5035500d8104203201100c0c20030068981203801c155100c0b0800b400200c040c0724143c60802c48a40030b1412000352003a420152520341d0314028010107907900c840034484d050100000700003e11290070320b400c9901e021300a5188d414200381c054810400801e1001890b190170030b0b8080c6003100b030034a030603482c0e0340030001c1e4501800455003804480c04510403960801d0341003010103100400511000010075070380d00082c4964642040421000407010410b5520118203e101818250724194074440011020f03581a0000b44280781d45900307120a0400034461002460b21051000c0e2402401a003080c0c030070050104010142c07a01c0e00c45040c00c54032410b103071000a0038000320030f11a00818000280c0a01c0c04c001e8214020300d10220a20000c0c0c0d4600c5581c2141941078581c141395890b001401e54249a00401d003030202074862000d080058400c01c00c855248140e0741e01c03907883d0642440024204002c00080c1410141401c2d028089541c0f03040c04240c100346c031071a280c1c03414404100c1c1d46029 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 454031834 1250 454030584 454030609
    0x62001021201060905190501020c091504111902030306130b060706060b030f0c090607020418020d0f0308240f010309080408031803061611070506030a1b02121602 71
    0x815880000603483e0740000b0b00c181a15801c0b111206200c2030a003491a1350b6001d0b105050059108003202c0350701b0700b004107150390001d000e441706c12841140781001c02e0540e001800491500c480001d280a0013100e850518a00d52826202451941c14400c0000b810118211600441582d803007400d0769243d504c110854054a03802141401231a5482c5245c02c5650411a00300d41e0912007000001c020321115000c550751010005c1c03846080855503001c0c840101190300d1010f40d80560300c100301016030b4030581d103079100510480711107082401900d401800540701a00d08880c4c2c0e0640d44400c0c0070094020031502680400342d0700b045400740d1140c0120090705101708080c02d50b1000040c04204000040010540415450b1802504460641c20325540d4002110b11514841d1401e82d400041c9104040703003051040607030100c944aa84a200041c16540260b500011150f80c0302444200142c61841e0008510114005000080c0340010360000700d00c510f20000c1e209500100c0d11000310351b07680a001a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 454033084 1250 454031834 454031857
    0x10204031203060312020c01050406031e090f03021c02070504090303021c0b041a0d0206030c070b25020d171305010f0905121c09030e030609010b0f0301020406200102 73
    0x1c1094035140c090000c1c00c49000c26079403000182d80c0700b0011800040c450703125541c10303902c8030b180500d090001c03001445005001140c45103902d09480340402035008155045020740f8a243d000c42444c90041c0c40c15107030301480d0300e00c1c0071494020402160049904011100290350104226840d850210b000f4803d020b03000503001003e58100306001141e500c90412054259070401860318880345100e2180402c104259012064070100801814103102460f004802000c4103410190140d940408007141110f402d408a44c49950710050001444508007440302180090300b10040a103e00038501c01185c0d20002c58200064049140305050010f16204160860000c014030340d0440c40400c00f425202c0000e03602480380c40008100070720710104540f680c0400e01000c109003803000000b032014011030b00040c2d0078031004c0c0d07424200d6500c05110452245031100000255214500b0401c000c40c1401e100142c00ba0b0700c18002440741d585c000c84000034402c285801c01d84200e0458410714060301c1103051811 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 454034334 1250 454033084 454033103
    0x50f0103140a0b0a080f48010206070e061605011407050315010f0c03080405120703080405070b190e1c080309120316030510030503040b280813210203090f030105010e0105090901020403 81
    0x35411402c0b038404031f10b0780070300340c4c2036803c15215010100d40d5403c460b4041544003800f04004042d10507091802295940b00c2d10003c9074151034500410b0a1080407502440440c1000041041c0ca00d041d82517403042c0082401c0c40c2880d9061598001c002460b90070340201402804000728040c03010070810f410480d80515002d541c0c2d568a885c0041c07042c04251002c940d10310407200c0115200c69484159180002003c0040805054141c0c08803084000200320f150441c0054010380b008030f0240e980c16000070b014a00c003540e00c1c00e0101c0303640c1c0303002910049241e00110500c04e000d1074a45c04000312020f101c0902e800700c1d03140c548107001d40240c08668401802880001000110708032507802920006100000030414182c421088200350400c60b980703440003860420008a10ba44c81c2281055942e0050610341d9400c0702c5070000324001c031044500b24000d0781c03000c03565200c40d2903e0291070320300e818107a00901865141009040110006000310341c80b4480d44400121840000d41c103403002175802a0010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 454035584 1250 454034334 454034443
    0x918080a021609050105061204080c010507051b210d06080a06090308010f080a080d02130609081e0307030318060203070c140a0b01050f0103140a0b0a080f 68
    0x699900002d05811850141050703000a001c0d030740d4800c090407184083d0480340b41c122a0304550301c40410061085401100034031003106105424480c0500c51a2251a003542e20821301c4c0491510003240c0c041c1c80300d80d0380f2400f6003003d104001d1084c01486106d541007103171140340340b000e0320b000b9108076007120050344206401e040c00d0040540140c0d0001e40283c40b00c1c0705690300c840760405081e40c0f5000d40001607000710031050008010354024401c1d5440000010305281c0b8901c05040c403800c0a0b48880001890f0f41814000d0001c00d10402c02580400710242518038240c80c40f0755240e005100c80503051640da80000316404051500410034681d00600c01c550301d00e09040c016248aa00316001c0e11083c00c01080e000da502000141d141801d60031040d000c001d60329080801030301e9206480e89a041540b508066107019421200b05030240c01c5040010903018074860501c660a041a07011b02540e901c203900103050f9090114161a0721800c00340d807275820750088a0320042403040503400c20390000011201c7c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 454036834 1250 454035584 454035587
    0x102031606051e0912071a1f0503190809010924090e0405030313020f030111030a051b031605070210020f010509031306050d0f0203090a031106040305040918080a 71
    0x18820300d10325403003449000300911818440b41003295000784c1544038550300584420340703c0c098502e00344203603c182c0c0304080d03ca050f001429400d4455140000b01d9008000c1640310f0b14440e500545010707001060600c410b44141404009040c0d4060501400011a010664494102840589045507603c00b200b1a250a009980b130400306030400000c000405c04034401505003030942c0200c0c0c02800460030b64481c4111082900b140708401ca0f40401400260029500c080c01060f28000440c2005512403600844100a403036000308080e8030403080b2130f10758100800c6038055a0304002c103698602166001c903c1c00351241c4c4161500a50b0180c480c0700300c0d102c0d06500046001103405910024000d58a485120f55034a0041c0002c00c2c44204034041c042c45264816405031aa035003e404c00400c451040e504c42c2405c0381d00035145054250425005d1405240e01301c80303070450074504480104000c1c5400d0710000d18a000d1401440d0402da222000059401450803540c043c0350b8110010307035940c2d40d10640 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 454038084 1250 454036834 454036841
    0x1505062802070e070810140409050f070501091a0307230d060303030b0d080d0c170f01050111030c060c03040f0c06080a0b030703120c0507030c0303050301030c0e10140102031606 78
    0x3030300740324031030f1007000601e56840380c41124040e00c1c00c4000c220180741440d44d000700d941070500c00203400a50300c07440c0c4030200c0e6003003106407201c1030600701902d05941803400040a0104036005441a054109020b5102140c400101c0c2e0340301c040380c608450203850b00304100740300204068102c003c0380b4010509240d17450090b4030010407a403003501c0c20400c01ea00501848082d69100001400d028001e0001051a00e0b041e08407030410181460031911030010711010000104080c1d400410f5144500d006219550304400040301e46841d1100a609104a2800180c0c0e2401d00400540d031101c0048041010400114403903c05243d0024920400035200c0707c0040242d5021600c44036410700340028404c46c1e04002c100d5109481c3c2140e1918480034003941c090390230684d80032080300c03144101440000441c000411241c0914401d80d1090780d29490341c102104082020341144071601030000c01d0082c5a503e1101e03102c101d448041d45110041d2410005030700b1801070301310303541181e0f06011048007001203550 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 454039334 1250 454038084 454038089
    0x18090d030b03011503060515060d060914090c0d0f02030d020c040615080f0c130b03010501170906180f10050103060f2309010f02072103150506280207 66
    0x40e03081021141d0601003600b03135a101c9030f8041d408607898409202041083c0c0140790700003002d20030031401083d02000f1a5159000041910850383c1d500018030200d1582e005204c201250400c003852903080200f2200e40310524010710314410003407610540104400c110104950540060640c0c0c2d000f01407550194803900b1403096540718a1914601003200354a85c2b00d0340d00c501070300d40d964000700d513107a40a040b00d442000c4c10403e90410280805042d003000d0507c0c040107448550764042e269450b20001605070404200c1181001c9255002c10140b0940050030343d520542c440b01203903100251190441c2444054440e800352405044c108110724000d5812050499109880c1080b204000780340343c7d42141c03c0741d00c4840505020003182034a80000402040e0007220140001400141403e20101240e000342e0781100d8201450f610b1407500c0c00040c5401c410080d26040c180b2444649011500e5418890b000700d45c8240c502180d41c603e0a8492011001c40d01c1611404122640c000d00f030180d0740310600d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 454040584 1250 454039334 454039337
    0xb040219020d110a200d03110615060901050d0f15030b0603030a05040621230901200a050408120c061609050f18040602130902030c090f18090d 63
    0x414a022032040c3c0001540742d583c0c2001e80000d448079541c0c507070448900c0480ca0703481c0701d055000300e090795a05581140514401e4030703403041c5910b6080c039180c20a00001c090b1030f122540780340420900d440d1581164018082460b1003a9030762070352501c0c040184031645a1000082c9032040000072007904240c840c0607a4050030703d035259581d50b1410513a03248510b05002000a5042c0400c000301c5004510580402c454000f0500d4464042292042141c00081005400c280003519508024240700e00040c0c2201140000b4061071100349948900d0090301983d172410b0000c001800780003280309605540260682c00c09036240030703c00724026141074000701c032010280e00906021840303034a03800c04103810340c52543d00d0b54089079280008015050021290068001c0070541c44500c11920f030030700c941d01c40e41c803c0b180142c803183c0700c0592a0549002d6005071140c90b00c10410701c2108000c0409881d25000201c0ea03100304143c2040c08200c001802e1000f0412412446090103005000460380c000000100e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 454041834 1250 454040584 454040593
    0x5030406301a09060f0f01020a050f070e071e050901050c150103060b060328061d090712020a0308071406040303050603060f040f030c170a031d0303010e0c07060b04021902 75
    0x12508000f619402512015800201e03030942d2119400c040319000c200701d40500540c6d00c0c0b9101c644405040170902070031540703d90024075044c41032049417655260020841d26004070b5060140c40c040504050183c0000c09100020920001e02c2c2c1c450300850310b1000045040e01e10203ca0440803454200c02800100c650b141008000c006a08196050303c0c8254080e10002c403001c100003a40c401c12420f00c14190f16400c0d12070901061182212802c3d03c1581c000f0182d9540926003447d50f64101005a08105000405541c1d0b003000740c1d68800e0000f0a0f40e40001d89959204500e14005600303022104880000f4010407007000189a01544680c0c4903100c2602610f40c40d0362000c80b5224007240c1154020303d1444064030780d0012912071402500c0907445400d2010490001c0746844007250401c4540f100080e40b10018081c1207502e04106e40840c9142c07030000c504550400484440d0b201e002040480c9051012401909101340c54214803c0f440c80070f4001c569920b00c0d0072400411480c40307050080035205 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 454043084 1250 454041834 454041881
    0x60409050603061509040807020f1e1003050712020306040605040c0f18061710050301060f1a0f0a050c0709060e04140a021513050307091d0a0503040630 67
    0x1400c41c0d4402c01340004012070140d0307595a50300b002c00e81041c04140d800c95890810244103444000302c2e800940d44c5880e04103060b42c06582005017070504206945e0070942440c00740300c4c00e16004428081041e10041d000350b01d0359190700100f4000c003055440300e68807a0402101340710300c540103800031030311084a540349542c010403025204001111440340740009441398024140450b007411180341c01510464596640955607400030f400e550b143e401c45c1c030010405143c10811140746505004204003900745803814130a01c0ca079a0889409a401090300348140024203502c841d00034400003019103070b0004100000f135100e202a144561045038212601580802c40005c540000904408495070080c82502641c0b1221806a0581c0100e107002100130381c000004a402d40e820701541000e400c6d180380c0028121b0b44040c0f0642d5010b005194010030340c00085040380441c0000c0125020307241107040c10781080640386018007041e072440803c415407403001a15417071103642a4014141c4e44c64580e050041510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 454044334 1250 454043084 454043101
    0x30b0111030a050d0903032910020f120702060403121e030b0d060216170c071d040813092307020d080f06010309050636061803040506040905060306 65
    0xc180301c0c42c2000710300144112183c0308401c0e001818214424517000c1180d0304031151540e412041e130340c1e02501041c1d4189820f50541881e0150324212040e0348020020714440001481d101c2002d16506112000006841810354480304102d8000307680c0154044199198640b00070306000c080200c0c0e4000301c1014601b800100d1090184017000d0800401000440b2901d80e100402507010110710692040041f11540118450030440303000e8414003a040c56562501d0032060341000d00d50340208004c0340750350103c02240502c1d603450a81c45640b0000389030b50758000340b64000410301190b000700e0501b810040c866142c02090200000e502d60041c4001c03c40f81c079075130700a070385a8111100c6480010400350000301c60003007071045542c109006060014480300d042c0c40d1030382022001c684e0b1841d00b80130b82c2c10200080c00a8004043e1132111100740b2480204603c040c103480e03080160010f601c0c0302066001d138140c1402441281c00030b0100900c204e07500c44c0e0319400c0c02c002d00360447d11a4440d0142d000022140c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 454045584 1250 454044334 454044337
    0xa18211b03021b01031d0a02210703140106090603050c010315061209170403030c0b0615030a020c0c0604290405010c02130f02040b0304050d020d0e040b0619030b011103 74
    0x180e5142c1c01410640c0304071152203000c0000450f80c0d904241e15180c10600859034015441c60340c5003001e0142102030000d005010a514070240041c05043e01800700f1007036032502041131000ea95010242e0084030000c4018540504100e0b044560402d181003400010040006880002c007042038805201c3c88003080344412013030b2014421540030031040340c44019690b645034401c6076550301c15211130400c1e89030442c1e40003140d04182c01c100c012413001010034060180c50400e4035845103044491940104000b069001e40d400080c10624106030089076032644ca01c010b20180c0c2800e840900601e846941d18450854180584504006518070410790140c8000c02c2e60225802c1c3c40040c1c6801c2c07014941ea50034000d0f0f014020380d20030302003a41d50001c030200e091b0a0004200a04003440c02c03a480342441e091840c10700103a80501e1080d98043e0b100d594900d5006600c03400c0403030381142c000034039080c000c2c049445417280c8603e0f400781c00c40c0c901c04c250b8410f4041d0b00200b04502c00307a0b00c85071100d8281e02c2d4185e49 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 454046834 1250 454045584 454045637
    0x50319020f01120f052e08030405010e030c0d03180504150e0c0c070303021c0c0c171e030d0b0d051c050702030a050615180a1821 57
    0x20070351030a014902c1d405504482e030300002c0e0100004480034002e20880840320103540d03054a01e0710380c142c0151207025042c8081d000400d004e0407a203c032071411685565030310440c825603051014003244051942d900f03001c40c184201d0003420040352048189401000d640b448911440c940c030301c5c05000f05403820a407180d8003000050100c0d001c410350401e211041c691400070080307414468200b001106a18040c00008002d41c4241c006081101074181401f0800c4510120b00c01005005090200842c4104a03000c04a90b15842c900c1c842c03544801c1c21504040f107405015120440e00c141c140311041000004110255251004010b2071365010204000000c0e0088003a05a900c50302c042849807005076801c1d40c04c0701590a082d0305d00481a80402e081c40170aa0080d64039400a00401000e0055035003c4480020121074051040300020800003a00e540a0415004559500b510403400c000b16500c0d000c900b5000144c1c880c0c88030002c00f03007070106131340e0142c440c0005008503524181008440840c100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 454048084 1250 454046834 454046839
    0x40e16081b060c01090c0b0a0207150509010c1e0c0f0e0c18030a0f0503120601030506010f031a150418090209040b09160b0901020708120301121502031005031902 71
    0x31855254010031a0715040660700e032140395601c94204000410a4403404001e007c0c160445464540d41d400180c1440740c80d601c480440400e0038841e520044d4010100c44a2000c03d0900079050700d41401c12925203105251409142e0340041d20748400e01c000d05108d5400c0300c200c08441c4494070345803404c12004e44019a0000b021001c1849154054190702500100710f140c0a412502c0d0440f2540301d58011000212042ea1941c00008010700c01280d811440d5900c140d007030030240b1031400c10000007401c0c140308000d5001016a610170300011100724041281e4080401018a00d101c5040700c10315a6651161007400005520381d41c1c40403190006005080d1860380081c120499907440307841c0c1e10380508008019450b10701500c00c402c803c11582d114920702034104a10700a45510035980068600508d50b01f00700210b41c40017440071402d04460040780c4c10b44d00091782c1020341000c1ca1801219000d60703412502e813082d00110030018220044642c120403520214216443e900c9030600136900d01c03000d200c01a4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 454049334 1250 454048084 454048123
    0x170c2d0702150c10020307020d03050105010807030c0306052106070804150507022d010b0906102007030b2706160c06060e0103021503190b0a05040e1608 67
    0x50161800703419000301164000c08641c500420822180d04104e9080d5403007502c2030b404400c2c07003112541000741541000320717800d0811455051000107021000c0003060101010b4640c8124034130144a50031600041401030701800100340c581480310429800c01200e5580c13440b9031800a01c815100751035190089412280880c12076070070744106006410010500c2080d40b00702030341c800055200901290003d81407210b0707840c69025858056082d6519444000d1007422801d06101c03d55031240042800e200b0320f8140182e46242000c2c8820110305488814001c60284030000420b01901f4200c0c14400c0000710086500320f41c00542ca00080406460406070590001d40080c00e10011031917501c0807820fa40c10038642c000007542d00d08041d0707107494000318000c000920041085040c08500c1e28100806c074902c04d81586484103250700811400d0300f90a01e00c0b52180340307c2c041c03a1038901031000948400340c8144903c0000074440c40da204015520199a445007413400500094042003a4429100c50701510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 454050584 1250 454049334 454049347
    0x1080309102c0409020613090b040903201905070e070507050a11010905040930080a050709181e020c0718061e0303080c04030b0c0a170c2d 61
    0xc2c80c9000380c10b030f80c200b0344d20402d000141e81c624001e40210303802640640700301420075200030103841d00081c4060085003880344460020350050305007215001074051510380f0510380b03141d6a1a250540411550844400703918100340f09010a9000603942043c4220b009900c9180c000c41e1a4805c1c02c002402d241c11904440c4005070a1341d04100240005241c80050543c4560005045400e035440494448060b000040c41b041004100b0542c0d03640032560914580c1e801901c00f40c1621401400b94151079601e1002403140b07800760f184075001d02809011012400c41d0441c40c40014100c2211031031311001040c940550f502d546008480401c254000a000e04c0c03803801c50348c00190400c0302ca10b1313500d20340ca40e840800c080b082d000400b4400c0c0c0400c00d140035003600c6c5060180604602405000002c0350800082c0081120300e01c03480e030080c007c0d820441d07031070304403507011902c090459980d00000c015010510000300c11410141c00210740200c00c0400038402c500c407040f04c1440d000140c0d80016002e1084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 454051834 1250 454050584 454050647
    0x90708120901051b160515030708060904060e0109030c0201030b3001020c0d0f1209080403030807110703140c090103150203040c0e010b03010906121112030d050108030910 75
    0x280001c1c00003515450b9101c000384c1415420030f8043c0d1544e180400030000100068600981404000e640c001d00301072550a09040040800e240180164003c0700c0c0c20011800300300b61588007022807088000200822442444c00406103181d010b001e0780080e0404003035965030301e8054040b10001c00d44a00700342c4000d80ba4560b07232401c1c0b910310803c040b465600740a20201403106010034140843d1b150baa480b10342c00d0100f4050b108074548582900910310345200039000034080411103041d00e4241c10440250f680703d4600b1181400d02e212034809034000c2c0007000082141d21855502850609011390301882803840134855105000d01c130140a4002e07402102200c12190390055400a01440c4800061602c8444946028100380d0011495240001c010080007803944a0400a011800709001c1030a41d2500d074501c906075000c08551150a5000c241d500810040084891030201d154044c0034035a9149500c076104c1d00000c0d0100e010303070f0a0f190909000c80c0b042449e00f00c0007407860024846401000724 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 454053084 1250 454051834 454051837
    0x106110a060b040b031c091e0b09130e01050403030513020a1505120405060906060f0609090718030c170304121106070b0906040203070b090102030a1b1a09070812090105 74
    0x70068105540b1102c0c202c540d201402811b02100500d1050b00025074146001009019990f20420346840302031005c0f02c42070703050b91140c01100d0f102107030142c40b03810b00750000f1068010f40c140030045610b80100314819100c103401445c8280c2c004d4504000503035800030703048481d8800c258002d501081030703c41030000096030410345019141e24034105040010301548001c0c442426a004d840c03560200003040140003041001d55803082c02903d522081e000c024010032900e001c1d0741041481007042000281c20944103205100f0b007042e842c8107c014035940d904006145210302c1c007980384445080442e101c1d00b04030000486040382c1c02c81269400d8a26552900e40c80950000c051540c080000c01a03440411000030322507004081d402c010b0045c500301032041600d480300550281e040000c0c04c0c482000315a07004019906801e031503081000807074811149080441217082070052240003a0721010b20f00d180500c00340da12612014040382d581d107803194000303a03844850a6400b0383d00041040311300c042d54070400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 454054334 1250 454053084 454053101
    0x105071401090b04030801140a180e0a050d050c0c180601051e03040606060f08150d060e0a0b04031704080409020f0c0d080a06090203060916090b210106110a06 70
    0xb4850301a56140421841c09480590000783e0020040c0918403621179440c0a4400803125950f1040c82c182c032142c4c49907002202c2c4110169280c004060703152042c4046500300d80d000041c2c44001e0b940c0440600140c03c2566203a4080c41804c020035100e040030103100701148200303125000180d5445004440d243d1040715890303444510403510040d6480c07860003660040d4800d100100d051802d15600a010740744254060081241c04410b100508500c4000342c00340d41c0007600c0e0042e4042c46400c0a1000d0300300d1030106100d9108000e90702003406800407100340201e01c80c1c0d480806a20369010100c1d64400d065902524105042104002c881c00550040c00c0140f104c514481c14092a0841d036410403040d0203070000841c1200e0300b000504c54242c440c8001030803d69100f103045061200102d9500e15004084e03d50425010040074882d82c041c03942500140301301c420642c1e0b614200f142600040c10505070030074207891000c0002c03520a00481c01490b55407944001031140b00d0882c0c40c1d0300d02400901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 454055584 1250 454054334 454054373
    0x2060702060f030a0605010e011e031a1302032d07030903110a060b092a0307030219030204050f040905250906060503160311070803041b08151005010507 67
    0x70020800b0180800b006184104621038000454514200014001a140c2c1c801c0701c1c1000303400d18010058180219a684510401380b5001400308200420000705071a030b042207a1380b004200c1c81d030381101c04540d0001c0d440351914404c2416030081071100d0200c40c102000041e030348030302403000141815102ea4060f005881c001c1c81c094491054040020b4100388942d401515030b079440f80310301521820310b04400d41d0066000440c41d180b803900b01c100ca50041045404c000da40280010214203414400e405541d150b00134121032181c0701c15940000b030000d500c0780c0714050003407106e0103441c00344e4034061065900c540e40190241036024688105904004109d00001c900b40400d4100454111402d20072607000e401c664540310740c2d0341000c9205100051a0007400010941020444051380418006664500313520810254980c0c81c7c0f0300d404c1d10241c4045040b4414890200b800146184000580d10010003206000103c1a142c02ca1030301c2500803a40142404100204040c00009022112051101548 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 454056834 1250 454055584 454055587
    0x90e0109050c07141b0604080c010e03010b0a080d08010617150d062d050108070e100302041a010815030706050c0307050106171209010f0305070201090506010816210206070206 77
    0xb540c3c2e00401c2d004103803441d82003980012400f038203079040960324207440101150a47c1c2041d01e00460b00d81e80e0415200b0300707810850710307003286095501e09421468554000030016124a9250120542e42c1c80c91081c031a0700050300c1e48000140c445c0501d010071445180f69400c407645694500b43d00b02c034040c1084200b81c021005a180c0c0d00410380501c03c0b40710b0b07640100c3c4a26007681b01150745500c0d0600305007045903030a10b440c1c01000050701c00107151003101c25194202041d6902d03095080540110b0764006500b060400355000482d00c090900b00b02080da00343c803070604648500313072142c4840340045000354059105000503c81c0600030300c040d0107000141c50440303103422216030781c16080d00d903d648040a204020f041034000b42d801806002c04142c0c030820346a0400b007075480000c1c4003c00d2031500105055603680030400c0c1d58800e405c40304286030418101c0b109940d41c4c4040607612441c110101c42e21502148010582c0f4004001d4106125120103248078070a1282c1c003000425409110203d0f4803100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 454058084 1250 454056834 454056847
    0x30c05032d090304140613060e281508060f090a0e0f0109060b0907020307080313080703020c0909010606050702120705130b0102010b010c02011b11220c090e0109050c 73
    0x15901036440c802c50402010b1a00e41e0b181410400301034040d2082d180c850041031003010a20065003410002312042d628110406000c80710102c0d507400c500c802c2201c22184110400200c0040e14680782c1c0445070369000681c02c01103881402c489010342505c8140d4001c0900e5810101403400186103030b00034100c0040080c40003104072001c0e1034a805900d203800241d45a0a005c01480070511410010060680f810b6500f4a03140400075240d01c900140100f80700300110210f2641c56581ea055051140d01100da16a21025410003940e0b5a1204025a11420004002030320010040c01a2000c85809031209410400c1c10b608100401d081801c07421421300c00c9090010366550303000b4448180216220340001d212010500082c25103221110003414000c1040c41c60005036800341c0c200c0e10750b070707450b050303407078144045d803801c4900e07582d4964090f81d0000e000145880081e40e822885041552084000c0001c0b600401003603d1000b0b01d485103980d0a03605c600100558034044d044036034442d400007041440c010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 454059334 1250 454058084 454058161
    0x20a0e16080705160507050a06020a05070905071b030819150302040203061201140a05070822050c191719032312040506070c050304170321040201020607030c0503 71
    0x207444c0401c2c1c50990250b00100098141040c400303020305100d01c040d119a4015856a9540759107a22070259043d58880000f000c0a1086600300040e0440c1600210348960301c0c1001480c8500c00d40700390030500b40c0c1025000c40c050f02d41c4110700b01d0010044200084521315000c000003034000403c49600710a110410703005c008800e109502c1450488940c98200c0e00b881150715046400050190341440081c90a007c040400c0e10302000d000061a22500c8001e43c462800e90b00b80382c0c030750700c1d07068100c0300142c0c0303401103201002d40c01c2041d5155031f900251901d41508169907280110440002da110600b01c4940109100c0c2180b05844001e1003180609003425410ba400d166001480c1700d15440b41c40c60502081000610815810800b1864413000071001921030390303220b1140344600c0c4100d0014000c0083c10718018001d0b9210000b40b6000300e100011180210340d5002000c0345e00f24014040c82d800035105901a00c0b91a02146159139130034107680d04c0350096000001c6d03041c1407003d41c0300e0340b030070045504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 454060584 1250 454059334 454059367
    0x15091406060d03210e0a0524040c0b0f07061e110f030402040509030c1009060606170a0e1005010b070302073006020d0e07080c0a05060f0904061a0403020a0e16080705 73
    0x107200b100140070440b00780c498100d23490030842d0400958101d1b0300502000c00d040c5000402543c00205200d40d0785c4450385403800c2c1c01d200b000c50041a1030b0a00900303504c0321481104140703500801c0c070400d1001080c9102e42c900144110005070b42c455100344085009400e15502842c0e0100c1d850707003124548070407012000e103000c500010124000351250f03940e104104860207100024101410040c514505c9140c3c080c500303201c02030051101d03981d211085500c144040017210380504d003121040099586461104070240e0014005030098441c8440000d104c0d1007218030466202e0a07410a912410480c4640c19a480c80491040d074a10f0303020b005d4030035070b45124801c810080701148000c0440c6490010100d0520152040075071203454030200402060310b500003180c00c000701c0940340c1c0f65290344800c00200141010740003000c55805541c4801520448640204140c0c1c1c000c40341080059551000071082c58001c461f941000003200004d5400720380900f40081c0c00c606282030041c2003103101640303030000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 454061834 1250 454060584 454060603
    0x70b09120f01050123060a0c1e050c10090506041701091e0510060b0708030907030f050f07090203060d020103050a0605090c040501170f0106080415091406060d03210e 73
    0x1039544000400004c024403074400241d0004103da903402005a05c0018079a004517101102880411852081040308814450501543ca032049031248507150420540c2e684060800c075016032600380c8130b20255406104e80c00100c2c2c400524040c502400d10b2080c012030040748911903200c0d92242c40c090300140d030100500400301f034100c0b28825030704050300b88103140284851140529503d401401e218007000d1004603901c003604071801994039103803030145c5460b125441c2d10292212508d00c0d081d4003004000315100000d0703918481120340309600d855900c0100c0c4404d50709941e01c2034100c0540001540650003843d400340440074000790007640c0d9008140180400c80b40070300c1a01000806003c65a007010607a102c003656100c82c04030324504030400c50710141d4180901800e00c25060002020000200f02c2da200304204244144551110b9241181e070020b12041814a9030061000140207070a00c0286030342040e806a681501c11810b03c01102c0e46007030512000c001054031003401d02c3e50440100551500e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 454063084 1250 454061834 454061863
    0x1805030613032d031406100e060903030a020a030f140901080a150b0a03180f02121911040e0a0c0306020a0203070c1503140103150b0f041407020c12070b0912 69
    0x1c0c1002e00340b4000342251308241c1490790b105170a01c14000c060b22850300c01e503c80c3c1e105040c20001001c000000801c07030301800300f55580c18440040c8220400e82e01103081d4182030f2103a2203494404a9640d000d0343e000d000c4940814120806000c01e030031542c42041020f4025115034000034102207403a40700b2000c2c00d0243c010f040c2203440050381c045481d5152141d08914014000000c00310440350303840d101500d0030042c0191142800708810502c0000c2884044000d128081c0801a04400c0e40f4200c000040401040c0d03102d5450034412144d002d102183c448000360f440643c1c9001c031400d41e51610000e4120007103010451106000450000c1c07041b0265001074030145000c03a0040c2d24002004040d510300701904002104918010000100400f01f5001d0140383c010000c0340c50071a41e000f084c801c4000300c06640e806402d201c7c40c14502104881018041c0d425039081e40c1c80150100107101480506003544201d6510500e410441101408003601d00c17490300800803070243d460401c0c070914001a0340145c24 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 454064334 1250 454063084 454063157
    0xf30210806010206010906050a1206060503100921080f0702070f03080d1b17090a0812060114030c0403030c0809060a050a08060a0f05040f0b060a0906180503061303 72
    0x81c19a0100301d050b0041103049402c1c41400d0038100401c0c0994030521804010341e429161140420a490b00400068840a0100c0c0d0740d9660782c500c18006040c42c6241078610442c00109101302e42c200410428074940d0603142d9190948410642044201004049400b180036080740803a01982c40380680c0d006500031514242c460145010b031404035590840c0005c1520b0110302c942c5080c03600700e868a0f0540c80364104442040d07883c1e046440c108200348100418031100040e0074420514071001d01c41c0180400c1e40c444120007041ca41800d264401901c40105112080c0300400001384a45d20000c0f00074814046079080442c2c02c804117100780c00c20b1408901043c004130300d00048981c0030f81c64551105003113030010350041c6400c004c502420312501a07640a01e0719101c0c1009071841c2900300c4880c0503c085d0045968601110001341507040c40d00820300010a4840301811041181d89244192140100034021a490700d0100900d0144c18a4003142404020300c0c511071552209035a061000003000c400e072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 454065584 1250 454064334 454064341
    0x5010c0e0306011757010806011209050c060703020102030115180603020901020f102301050303190c0804030b010302131401051504090908040f302108 66
    0x142810016000140002c420741300c040350010002450b1101c0d00c13189a00d503400c08100c0003e40368481030241000070a8410824000c07a00f00012420303482c0b02805541100c0d0001c0d9440c011134400c50151400e03400103042ca80316102c50f5400b54030041041e449402110707103c1d292000440c8840d0020801640540d50110042003141c800009403140d003540d510300040e10710321748410381044800c940039030300406501240354050342c0d0007003199112180d100c00c116081040d0702040d0700050540401c401018056412040004089c1d040149040e202c1c003c001d58100448002540807422210000a0420224807450404aa010401403014602030a5200b41a6045006010a490301d10502080003480d00d800551080c041001d020f040d074408a6217102010b0100150300b48074042c0e0f80021109914112001c420480700304001d004407282d0800380c0c3c0b40c803696001c0d0301c42e0001c1c1c8513517201c2000c11502c4000d801c02d22103201c0ba00d07165110304140c2e022004045044100c00d0b1501425201045211090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 454066834 1250 454065584 454065589
    0x7051002033108130b030405070618082116050c04050601080403020a03080601050408070608090c0103110409020a03140703140c0c0a0305211603060803030c0405190305010c0e 77
    0x80220780c1d0014554140305421040303241c0707001441480e0240c848200400d520130000181c4820340010b182401c81a40c0324140f0741419521880c0b18440c00c80410b001c20040020f0155482008044401c0300c00500000c1041150140d246201000900da4120081260003030b40a0444c1401000d18000c400030160114400300744011102c0244c00d80307051105400803c40003d40c0001d9079518198546040442501e8a03030058410b4000e0750050b49140c001c1c01c1c40071480b9648440d84501c501401c1c3c0032104107404480040d0122100c080b032501e5080800c203c180301124440c1c00400d80112a4580043d0045914101c100b812506440030b42c00241c90f041500065041e9581450b00b00079003102052034480c1800045565041d00100241442000300e81c400c0b508042c14070361342a09080807082c408a203001015140c8241c1206c3c0c2c94030200e840c0440229801e00d0000c1520b00ca080c456018070714280c00e11081010991003540070641c1144c240d03c020001920030b01075a41c01580640f02e80c00d0a0010303c04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 454068084 1250 454066834 454066861
    0x70201321209070b091c06050703240b25060603060623060406110c09090d090b0f0a030f0f09080a090e0405070501051b0601081005070503060a17030705100203 70
    0x9480c0382c80d405548144100101e480403210303410750494130224820800c0015003071070111500054081440e03c0b00308012030b5050341004520084403c00d06d202c10044180303c8003840b40500030007403540b00c180300030400544018040c20060700440c0c984452072840c2e40d0345034141d4105401c101e85640e2100c804100f611000080c1d1400300842c05456018900c60728003103a05409248130742003c01400ba40c0714543c00300305010740f1320000405403c02030246004207615990340b6250410b800003c00c24080040c21450410544141e40680c240b000d01c0c1425080f0110090300440610507001940d54aa058000e8034a104050851380300fa02c0081e11380c0356541d4080c10301100c0d41c0c0070080051042c810440080d8022890505480003420156214a0503e581c1482994000030084a5201d4170700042245407000410f40403150300c60500740074603540c2640888450109907031807508032000b50418040215072500c24084031700c07041c0803a42411496140c651500f010310605540072a030010030b0205030b400704407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 454069334 1250 454068084 454068091
    0x5130c03051e0105040f080313150c0807080405070608150301050f01090e010605010203030a050c0702100809120c0a030f02030c0304060507050c0d0506040605060d0b0c120f07050702013212 83
    0x20b000b0461443c013900c40f2040c0c2d0001c80d40061162500000003540c3c0480601090304c9150018858000801000702c0e030700c02800080503d0300401e44070700005091520456401d40301d5580603010300b0300c00746040010754410202902180040c0b190b02410020b0b40c600344200740c40f0f10040c1010710751039454a640030085840d962280301d0035904284042c030060f600002102d421038122240013a4590792845c200b00c5074024610025404084031000f514099448000c0c0b030b001e0743c5000195280034030409032020080c0308145900c15907420000c032400c08280514802c15401c82c190068030324107200840d2440c11a809600083e0201e400072a0b9a01400750070030010100f000d040d214032030220202d4451658a08000748020001611070000843d1515400188107039994041c090390b00c241400c040c00725968104045c8a1480d0f421240001c00111000a4090145049403a0380d4a4540350303400440b401810300c10559007614510414038290300050265221844c5e401e29070701e890f82c1e0050903851145001a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 454070584 1250 454069334 454069393
    0x108010b1c0f1425080a480902040513021c05090d3c0e030a12030b030a2301061203110f0705060a03021b010903120b0a1805130c0305 59
    0x500030300c10074000044681811ba0807120b505010b0341c0040544004005150b440c041d0611118141f50209544c0d00f0440c10021600e8218502c90b910b0b0040201203003d03078070031141d001021b94484020451503500a0010400708082e1541c0d81d02c5c500c40f024182d03042070b02e144802d0f90101030541586030388014032500c0103002c4945401840101c607242181c0d1010542d645c4003180b2107042156025004103081e030316514002d025294080e007117090200c0715401c02c1c4540404282000d03d21002442d02041145801d540f000c40400b140720022054101d040381c0c903041741103035943c600000c0741c1c0c40c1110380e505007654466036907624030420061803e410310703628000c0c0e200b039907229140621599698034141c41c1c0340700d030301d1a0060319050110048000b1072405c501920440d4030300803a080500d079221501030710103643c400c81880000b154000340141825680b00f1480d08113550340b910b80703c0204d40e421050300840440035452881a2607181c1c41c1e030801803644100d81c0c550000e00d1f85c01007407040d2844540c14045d103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 454071834 1250 454070584 454070653
    0x9010c140303090d0c0c031712010303020607080a020903070b0d0e120903151302220c180b040e0f0405010b03030c1515030604030c0804091509050108010b1c0f14 71
    0x70386d40340400800c1900000342084114000100c2034100c09060703c0700c618810061907001c1d652800d029440e8030054138010001074400000801003c018001c0f0365560801400400b40249040c40200003034110b21440d48100317407502e0403401c090904102d2440206520402c02d540c0340c0c10603080600c1c2503212018022484030306002c000c0c802604042d9240540d8058400e0300f035480c0c004032403003500c4c0d0f044008507418038901540a047c1a030b22820417910000104120061a40c0710b100780b1b6107034011403140000c104101d100190203d11040d0f1041d40181c4903000200d46100780000190840e04512090492544a001501c021101e040c0c0e00c03580003842003040030f60884c0320b18040786c0c8030000100054240031003202810100050a41114018a020346e820880a9011088400001c445224a090480c10a0000305140764180b1442040d190024130201d8105418045416554600030f015591000b0300100c160114209510030340582c040580504201c40d0000d080301c0c03034491002080014001d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 454073084 1250 454071834 454071857
    0x60503011d07060c0503091c021816110a080705060703200405060702030c19052103070f06020708030c031f0501050306060c01240f1a090609010c140303090d 69
    0x115900b810780310700340f40004c3c0540c0f0030300300f040c07443c454840c0803901f180144400000320411111015002c6200f164103c1440d007081b031002c01c00c0202521707640e40e03034020300400d9405140a440780c0241d2941c0c03841034401c140315903220b807485500700c80425246030b00000e0402c04965494420b0710003c6d100d591103100c0d0340705138070320891140c0a80c2c050f00b0b000383d00c0050701d001992f90030001303025003490040c111752203420343d5100e6080d40d5129100d140c0c080c020a00c80c4800482003020341d01c6400e5104401141041425110503005401c21075064403120f1b030030800d910220341590011482550041e08075941d03810410300b607035401c5d00310300c3d40000021072388441400240c1e4454101c13a004002164495210003e0341100e900518200c8024107400b8600c02d41081241c070501d420800b110360700c6917003e812540d5480030700e4800c01c40241092a86104000040852600d4005041140418076100040300c80e00c0e0b541504a1260348021051940040100100850200b00115440c120303490f040c5003542c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 454074334 1250 454073084 454073141
    0x30c160609061d0d0c06020d11060f070e01090803030c0315060715020d0b040615260106031a1315120809060702040908130602011103010602100f06050d030306050301 73
    0x1001d010003a42c3c3e0030054540400c903030b50315030300e040c03103243c0261482e800569038143c01385d0f540b2074446150003c1b90320707902d0500c1c4515012914034816143d80f1580089641c81c00340407141c9031003054403603044c02845400071903940c03001c1014503c03c00c0310f4144644d032424010f42c622665811030704c026100303100400001c0d0020350003071211140b5101e91200541c41d1007240100f40c001d800c6140030303d6001850960000b8200811550076201a0303980e885803c0c01035100c0c00d5981034841781ea03980741503000d011001007003160301c291f1016551801f624a42900800880002611103ca2449000d90307030780c6403403221182000415942d4010400c3c1002c9030071424081e40c40c00b840d805030714075680c072480d0040340340b0003551110340001500303d42c040d8031203681d80340b507002000000c000c9006601c0150700e00b0014210100700c0e1421070b41a5500c540081c403c48075949401c2c400703400040d814517205600d40000080c181c645086031001d00744242c074081100e0f81810140340c210350090b1040078244118a01200616 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 454075584 1250 454074334 454074347
    0x60215011d04050118050304030b0105120601062a0813142d090106080412030b1f0c0209010b0403110d390308040e0601111b0f03030c16060906 63
    0x210780100c20040ea503038880c10941d00400c0c1d54a5644d541c1c40781004180308001d800b000030030507070303128440010860740c0f00c0041c8091203174042d40c40d807032590144005101d0310340102c0c0021443e00c01c4c0d000d80014a9040c4460403000c0c0d0349418200d03a61000401d08086a054041d8864081d05028402141985280000517092004461003c280405915503030715034101039a2600401c034009803058000d960b5904000b0050305d0116010b807020342c020550413034064800c1c0a584000d0400605019040b03038124055807204401c842400e0a200300441071340c0040e1184041c89000b040000722064440746103041c44034441d10701807440c0d403080c0d10000052000172034040d50090344404441401d401c695420114200f18264500e44000d0100480c0c800410412008002c10070346d04042400c00700343c0c40d8400150382e551520789140c072554004009000005260890352004000018480c00c40b03100300350042400c5070303c0315a41c030a880d000304102c1d4110400d40054000241258a400c0e06018540306d0010881c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 454076834 1250 454075584 454075619
    0x50f01030b240d0212060307080c01020c0111010e06070201051801180605040804091b030c0203071502090d0f0b1f0305031206043801050f0301090c020a0506040c06021501 75
    0x501c565903a41c0740c5615400645503d0819408219580c0c103043c0103e40d451181182e200d40b00e407284074000f180891010032403903000034068000b0101a41b429005480035215961a50495075840c5409803445070100900d43c02414140c0002450741000c50302d54000754800c6400700d81b0b0742e041c042c0e101b04240200c0025803806400020000d15034486151001c0310f072080741c0c0300008141c100030101030441c040c50610414203620781c40c1041480c0c0304c2c400c01d9841e802000805000141c1605400c0c003110710540003010084001442d0408100303096881c0410f140c8070010a0f11288103034020441b85034158600e4545203000880645030452465403091703900d200308078142c000f0581007000b09100c2d4a85030005100400500c80c10005200b0000e000d030f070103071440c000242c08a8800040c0c1e00841d4055811184503a400c0c0541d0391460f801c0001d0080644102d02d5030394218421407080101058051120a000d64407861010341114034100d4024580402d8001e003102c080242d1004103c9c107402c0f1140b4015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 454078084 1250 454076834 454076869
    0x30a0f0206030405030903060903030a200a140c01020a0302030109061403100f0b0907030218150d090825030207090212130f120e03010509010e0c06160c060801050f01030b 75
    0x2d5079520707441d0113820340c0240104d181d014410303403040c441c0e031100c0840518415a08024100b080741c1c0720400524a2240100342c07208804010008440914464030042c566001d610600e03038a400c04274040242284e00c0340101d50006540400188001001800358600605400e6103c5d034007101024002510303120f5507000003142d9541c030310080000b800c031900022001e22009003004128604548050040c6d80003484010f0a078a028400c00b10504e05165041d12602b0100205400e11215584070b000070100801c1c16610b44a00b442800c01a190302c0b030507111500c0b1004a150a003618130318000c0c0c13504001da0061205a40140080e94000c418206d9240d440501d0355807240c40101c981c00c0c0b03a04000700110004d0300011460008011050300484014540001030303008002a60b54254420f00701d81001e030204c041a086071140c99900e24192001e020b081c1310f0a515007003080e04070350703c1042d2a9802ea100c60f0200350301d00010410341c0382485071641c181c1020709040c0031580752500001c103048000f000d04807 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 454079334 1250 454078084 454078087
    0x1d070302011b1a09160308030f090706080105150f040f05030d03180b1306240806240a2705130b011a211005011e1b020d03090311030a0f0206 62
    0x321075540401c5181c5c20180c081c00c100400f540c1700e050980180d4822070f0032080c1d01614401040ca880d1000407014101da045d544e80784160390070402040303507020fa204202d2560480070b0101c6c40c181114000200300030411044526002e0786801d01b407509240544100c0b40a1501d000785041024504010b00310140398401c503000354554407458660203804450b040544658503014402003031912042031052a40d0002c264000e44655a8840b9992540102d68840704482e1200e400c805c032a48440d0200d142c902c0c004c000410003911811385520144040074240302d4840b40400340e5404455a21450350403170703400d029642c1c82c0d408549501c030081e007040c0304465042c49800c4400304582c500800713031002d8211070303600c00000d0f50000052404103035041d241141501c1c41480002615030040c0c0030102c03000d4820145001d4940000b0003503c06c040c402c0103210400703c8000382900142d980c124070121503072182d2506807190b4154100f0810110140030303500c0c0290b010080700d001150026405040309981110500e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 454080584 1250 454079334 454079341
    0x30f060402090a080d081b0901020c190b0c1507050304050d121112060a0902070308070c150e01020a080c040f0e180d0206090607020102030103241d070302011b1a 71
    0xe01c021007140d04c000164040c126204142030b0344140041d008151400c140c0001c20f4181201540c58419440074602681c4461043c9100f8140f810314012a486203c0390785001565981d07100000d03500c01048842e2031b80014201165419504116940260f0b003403400600b546030a80e9060b59800719400c81d2420f02600d4510036110002c039400c50780041110614480c0c8070710f05030400d0552a0001e0b81e00328801d15034210042030307a000030310989181c1c54055851903682d13110490701b5100d10b903c00e08180c1e5210420000c483d50b0003494091070b00311000e45c800040e520003010134000d255600c09040b1603640c40302000300300302941001980000707681150307940241c1a00c03040c1000c506032041401440042c01218610752805401081c0f551103104080c054869950f0740c81c0c4100c1c200d1009010050803402c1c2030b6103040d0103003120072283c0710381e61a80c0c0c0005a035041210101d01c5030f000d5051906036681c0498418001c55038803502505500a410100c0244400140e0ba074182c1480401e0102c0201403011002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 454081834 1250 454080584 454080589
    0x3060d050c041d010b040b010c0f030201060515030105010816021f020714150a0501030c170a20120105010f0e09100504030c020414060108070f09030203060f0604050c030f06040209 79
    0x200c074072185004208200341c84407100104860894004154001d500c0c00803d00c0c0359091901403030807000416595419080d16607541e2071003000c4404819000c565075820041003035195441c14a414140619915840758540030004210500080031090302600b4a881c1d10005038000a04188440c0c01c4101010000d245203036410081c02400400707864882e100342e41e01a2028041030400e1482d103030242c0503e556441c042c552068640030700c0b0050114070215010818010f141c015004000b02c0300301568505501500c506203004003219070001c0c071008035841e2030141e181c1980050392004804000b80501d6240040706d00815003d80b00b0000044184400900c040c4405c0c130040c20030002e550f03400c00040c200b50400412100411004900070703490100c0150350100360304c0032644281e0050b5101d81041d40c800703208464540b10000018140700c040d603801f00050342c1c203100f2107103d0740d007405400780940380c0b550821040c1d0f10003404030b04802c0010810700c41501741d02ca0724107500c0501a135016a466540e03902 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 454083084 1250 454081834 454081843
    0x21e0108041514010b1306020f0d03020f040b03100503071703030a0b0102070b040303030e0106090e06060f040e030f19030902101b0c060f020d050301060e0906040219181a03060d05 79
    0x1040040c20420300000c909511000007428840f4991b0502c04000741d107070310382030741c1c0c0750f02003d41103481da48503c420142c030340c0c031030340003088420250403925040a80d107071a1701c0c0b810703081a1403a2002c400031482c2070006040401020000f4410800100c1080d8410880c6585920015044402454440709070524590003003040000415100c4146c030741e95546d80c14014002c041d040c803090215401c040c00040c2400040c002c101100710503c01800392602c2344010444801005d440d00f0340c0050f180c01c0001c46c0b40800b440500f10000c0403038001581ca020321641180b44044c2103060405040c60400e007100540c503200f1103007110140f01c1c20000e07141d5030500140b150000070850300804c2d242e100c1c40045400c5601c00354038041c2e03418070b07000c23a0b8154a0244082d50140424040c43c40020200040041127107400101c030b5800c080007034801032a103145016404c109043d00486131012820142d840104040d500d611600103008661070b442c80b0380c0b4003556105080c80041c100368810700e401d02090003401401e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 454084334 1250 454083084 454083101
    0x5010b0306132603100801051f17010e120703080612031c0209040501032a1a090d0804031a0a06030f0221161811030103060c02190f021e01080415 64
    0x2d1180c0341e25048017000c0000d013040c0a400c540d0350030900804c0d41c1c1c0881d088400c0c4846084403c011082d030402103400c8080c0e01800c8c00d404103640724288106111000d121a8251980042c00d0350707074a00d02414040d10b60b040140546014054106050a00348004000c1d80e040280340a000031220048202400180c000c0481541d486032400700000100000c000c0d1603900300c0c2201044103000454071000a0480100b071181802a2503040480b054444070980205141d0f00010150350075142c042e00e5030703c496009600212040110b0414001020310089241540700707501f0a41440f10741d0869031840c1c03c9203620f070030090050310700480f9040c08850b0000907000b04d60f03104044500013810803251040e1710903144603500c401b15540c81240041095805000103014a501c0654038507440e60365000300401c1c00c1001002140a0907108894000c2c009400701080303070041c400c0402d0f495907401042072400044103d10038400c5030038801205a604405480e6200380c0100d40c4156084c0c040649501400140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 454085584 1250 454084334 454084403
    0x50a11030f0d0c23040906060c020a0522050103080307090b04080a0209041e050106090507030b1e01171003060b09070c1b0801090506090601351e030705010b030613 72
    0x10313094280f41c1142c1c4094070448a81c2c0f4814003141e580c50409603054504400b0194000180860a011031b09248805011b1030700021490240a10911405030448100780c1040310034100c00001e000310103074003d01c0305010b4441e03c1041440d00d4a4009620707601c1c44074041c02070003644080e0010b1300b84941c804407854403500f000e1012040d4100d91910328000c0099000348105540b914011070071140c072904c03814185d440c0c06081d610840c140282e058920b0824003070307184c2c10040341c403008942d41c0504440c1c00f4015420a00001130050662501c8416951038071491030145002c0c50811440661008032600320301e403c10302c1c0503031605811611203403002458021510329820701c0c04503000c00500281062003904201d05880381c0f40d807a62580440c084001541c000c22481b0501e20750220384404ca0354481503200001156411075128003c20006c4043d80c0340700b145500007044081c1440400c0c00f0305000341400320040c010501d000d001440000c40395003009032107070380d8400011017000d60b03000507a034031700018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 454086834 1250 454085584 454085627
    0x62d060403060e01020909150d0609051c0804030206072c040e0111041d0c04060809070504052d011505070f02130509070e01060206040f0201031b050a11030f0d0c 71
    0xc0480c80c0d8081c2d1b0083e903545000302401d0b000030b180d0300c031081c4c0c64503000e03500240489001d01a0341c6482018201c010800e4a141c0902d40f5503d03843d0601e051490305880040c2c88060303203440c0900b4041d0401200614010610a80440d0341228043c0240402d2000d40300400c030311441260000071030014202d50014505a41c84c04401c8440e03040c6a034003500c00c941e0f0804e440c0c03220b000c2da12441d8012a105450b5035021201c180800c0c0000c0740100d1a40d5403007640c200c102d0f84001d60b240300007000e990080d24084a469800c2011440c900844254101c00d03403403403440000d480d45070030f042ca5642d01319190010100403010030381e0400c20010300000016540c0050003c2494844d03250b0b031800070b200a03100410346100300c0d18005a4080040c503903d0484d00c0c0340d006000715503201d8694598140380c01404904040e0346240706408681d44952418000007030703079901c5880350b09135013001d8403401c90007901c1d4500d81d1050061a0421684404560f4001400d40b80426051040c290644560100c3c1c5020350142d401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 454088084 1250 454086834 454086851
    0x150510020f07080304050f01170727030b1605180603090f060a020301061e090b030a021605010902010e010e130f0b0915041401050634031205062d06040306 68
    0x8000001d00f040d03a401f120040d2401803000015242e8140e148082c0e001d03600901d0008070620f005164000b0310035100c00411032600a8078800c0d84182c5d48680084030310410070014881c500600540d41c0c0003204840c1040c51518925442c052051480c8451861003085c0000000d0307922202032005d58440302c2c402080300d100b0308041421702c019400902800c000142c510b40304030000b00c0da500003c841002c0c2074030707001c003801e0a00c41211030550006050200081d02040410566400e190398640342da03001c0d07400004d540600d0300c00101f1104642410504100c41c40c5011440759852808000c2d1810044c0400101c00302c080c217401380038000307030180680c3c0102c00004005480083c0da1031400415800c540c00c0008611104103c101c0c05070070302813148c104400f8402400d0701100700c8844002641040100240c44c00b42d03200da60700ca80070310282200060101030407407500c0c0c180c0c0e0040940110381102c10b106132402c40d01200d440d009102000035a4602032040281d015200c1c00300300c402454212405000007403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 454089334 1250 454088084 454088099
    0x50913021912140304032d0f061a041505040218100503160203040e04080a14030c1215150a0306080601060c050607021b010c032a050f01150510020f07 66
    0x20402c00305403501c0d14002482c01482d0404000c80c1c05495100c50420b030302550342c0403200d02c0c04407102050340149030000c1400c00458041040040c20501c134041c04104403d407082452220201417100a00880c00d1440014402c40103800e040152901076800603103891583c0300729590880c140d02d03601d4000c0e03106828a03c0c29a48072005500c1400700381c40d003c1c00c1c2a0000c00803070b5280b0891007419408140c503004100001c13410380040c042804903181a039905001c40b05058420341c030035100ca6401280025910014030715050320658801070360fa908002e03440c840c0010501c81081403020340246200001c1d4018406d020341e016802500b40201201e03529a150580900020300090094505100304000074900502c0010301205002c082d041405040040d41c005403808448000100c09000c4442c8045440703000352805929900d202ca0307900880c4003500c0c18000d0402e1003400803000141d0401000c0d0b4402c108901d0408100ea42c1a60050700542d0710000032418115111807120362406020750008450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 454090584 1250 454089334 454089359
    0x4110703110307030c0206031314011b030209060f2b0c11010e07030b07050f03160e0a0e0f100302031e01110901082a0a0207090f02040509130219 64
    0x952080d101d0444048441100c159203002e5181c00030b000801030340da00c40043c200140a950806180c0fa04104490060f070740c3c0c02c000714200445121969501c025005a4142188054000c07a002d400c046141c5101d160214800e4480c2a4150550030000a0b403142810391101c450b01031054002640304282d010b20560388089c1124510110015110910908140c1818801c1c200180b21080080944030324584d10600080f0005006405025080c007030b90740914924001140301e404020f41e00d0824044440c0003902901400d504603018002300385060000800c01e14105411655178028006241e8441c043d4001190072608000e409d401080e0408401e41440b9a004003100f8916000f40440c40b84260359003d01d00400311030354005802a4041403145103001904a0689990f0310b488040d04145075840c4140e5101c0c280324401680010010014100cda108030b0070320024581040d441d00745817400081020320b020388003007403120040d003125046580b143c90055007900c00c4082d06021981da00e4611018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 454091834 1250 454090584 454090597
    0x907030f1208010e06090a09080408012c12070f021504031406060105030c0a0309050f071508060901060f0f2703020f0f420408160b0f0a0e0411 63
    0x2c41c906100214030401e8511503d841014041d100b41610b5a074100a075010302045001951190700801000c01e0022080c011400c604410317800d54801c418904144003040d0004070410302064000550301d0440c1e40f5884200e80025400c034404600c1c0c1e00540c00081c2414403074098000191070000740010030801c5850f0710513031100c108800e50301a95590b00041d2020b00c802c4890120034401000541c0b1260701a170310054070a405482110039005907411000c4c0781206c1900000c1c40d01080c4ca4050f0111a4020007007507025105980d070340c04d00e500d40301000d45981501d5510a0500104d04850403840b88a040109040c100102981c00c04444200c88100c2c402d5260000340d0041c8841c030f944468505001c0544250181c001d055000260900c1900ca00381c400100301d0080d45183c13441080b50110311721714495030720f819900b1800380c2e80c0d0702e844106440d1443d4a08013420407a0500b504105c040c03002402c0d10014560b82400560301c10064100719200030240762465401460f101c00707c03c0817004100907100c4c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 454093084 1250 454091834 454091837
    0x803040f060215091e07030803180610031e080904051006231e1e0310052403060609031b09070c120e04020c010f0e1e03030f0907030f12 60
    0x1026044800408240412680b00490350300c8000349909503985e280c02540803901c403205580f01d03903440f681d80000c994015603551441c502d800e00d040ba00380c0402d0010503000760301540c049030b03164510b5a0301101d41a2003059117101902c0c0840070301c00d2100d058100e47e05100300500400461134150039400707440300c02c2e000701c40c0098008071840a8100101e0080b07000140081c104505044100b007910311300c2d00700344640041140c018000f94880d103416003500380c080382e680c000750350f00d03498110864800c408656210f240300302180b81d00000003075840030424403480100314405603695610f0b4007081c51842051f080941600c01c14020700311149503480d5001c0384001c00c980d900240c2c4c86440e8100d0f04640f0b03c0d034014005185500109000d0b5008141c208070740310307000d0009410802c1d2030035458216000e05da140e13a4002d03140c0018045e071710000d11681000c034282c2c0e08500320040300d6614403030ba40d000c0104a04040900345001c04c802420800c604c0008581c841c1d800c400f220180e16105189038422820f400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 454094334 1250 454093084 454093093
    0x30d080901050901021c02220603090b0a05130201110f07030b0114030f031c09061a0301061505121e09030406120603030f0302090a0b04060c020f0409050717070803040f0602 76
    0x14400d0106008031075207040d8556602d60201b40800050f0002e510403440c04200304070101d0903035141c10740031803050001d00c41c0d07440c00105a901c0d400c1c002d8200d0401011203075203d103071008020100b00d20a12048480381c0a00c1c19880c0303036642c0e08105203401c1100c200c042c1035200300d480000070401c0c5210464181c030518008040f41c407486c00f09259072080c0641181c00140c00c20310455502001c201110000e038402c818010812030320a840e9070048803c0e0202140703000e03404030740703180782030600b4042d400007031807020240e04c0280c0c0d440b080200349025000c51288082490790201e14005a00d00c203110b1802951500b8001600300700d05121350340d600c944941000b01c0c0c40c14580200401140c40b60f041207903015110102d072146160411002940807502c1194042860107004c40c44242100140001c2c0180e900c510001f104180100103249141180d061321881c24100760700001800420716200715032040c0c0850060312400802e4031b0508a883e0400001c610003c200002c034051007600441c01c0361283d800f900c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 454095584 1250 454094334 454094341
    0x1020a0e030a03020712050106050402030a0f05092a03010f0c1e180603020a2006060102101802040207020d051b130e0c1003021b0102030402010809030412120c02030d08090105 77
    0x9034542d0050180034026810034013041085d0600301d200d1000007841840001405c5480340c0c0040c0880e0020b80782806501d81d2480c0400f038001031840780640060844006116011406103100e10340958000300c8682d0301c101403030349001500d00750043c0c9401205a20309004031100b105004110350640089451103141714280608094060407107a0f4440104500c0055810305002c0203402079400f00e28450100419100d607203d0a42a0f10904042a00c514002d07108a04180c00024604035080032a44417840c5064a03101c0a400d5070000310b444254155401b503110040703400021465103481b0b40103045801503500302c0030400204421030b481c01904444e003170750580b581d03000107046400e403000bc103000e544040c000040c54030700300d080721034121203500d409403800050030344000081c01081d01d408100ea4001c0280310441d030b00642d95542c044400001941010314000042610341780a031005444845098111075020b8445e600d00380c91950042c0071600c48403d040c0e4000e040000840d40140303694a0507010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 454096834 1250 454095584 454095589
    0x402030c060403030c0303021b1c18051e1c1506210b04240209100e030304090207081e0d2a320310140603010306021c050901020a0e 58
    0x355000d40c1e4142d0717106440b00320b490f501038000f03601401030701c4480100d42e52100d55a04c0b041268050300303c560303450381e8803851980c48041c1601056140007210517032418800c0c03100b5218205207180080c4400460400400064041003483c03081d90b0640586800c0a84684107205c81c0d4012510400740107907081040b00c5d5515110b0000703c0c070240702410f1a1145400d0704c8080340100b103240e80c0050103090000000f0400042d442c24505004108464054000c1245021480d05007032070071090700d0344e04018036040b0100000035128807032402036114203980070840f9014815404261020801c1c0480c01c1c2c100e0b020401c0c4141c6454014896404070141072409100b8a95150744a24655810616020304a540b09200c1a100d1403442480702c00f002d040440d0700701000103041d030003400c942510f210140e034070308080c0e030b0f400790201c40354011f111088441c00e851200c944540044904684d00490016202c9500c443c054216044840030480c40e03d080c54280040e01c4410750080c02c0301c012a80303c052484c1c0720b1205 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 454098084 1250 454096834 454096837
    0x4140c0a050a031113020a0c0c080604030512090a02150405041d0304050f18040b0412080c0a080a020d060e010f1e0b03060307080f030306011d0d02012003040e0402030c06 75
    0x1035140c202e0050181007001801140135142541d40082099040400c0c201e510812600103c2000000452031205034050000f29414803000d400171364042c111619168401400a02c01c44520b91ba13011260000245045814400c1d0000f096006260381c0310362200748104207541c0c103e40100c51107140707480144045402003001c1104620b002501440c00c02e4580420002180c003071a000ca5040314003c9281d083d0801c2c0c007400359214030b2296811440714105402c180103500320b84080c1b0414030550740c0070702440c20403076406e442c46c00d5100d142000e0503590b00c00d00300006e8017440e4045e4100600700040819a4044041c480741a1941d28a41123b42c0d5641e1548000d60141550541190200da1505004921980c0d005580c00706024044810207552264003901d0100b0060507102103800c04030510025607800503031401070340140c0841014a100c0c10000801e004440e8030024140030402c0d00441e00e00044c0b0038090103404118068039100c0c1c0c1e5070490800c940c442290102c3c0b00380180311410080c3e1800c45e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 454099334 1250 454098084 454098089
    0xe09070e100e060c100b0102030307080105150c150601020d031401120f020a14180108150603120a0c17030c0304030e030a02090103030c050c04050601020c2704140c0a 73
    0xa44203104448140c06000007104000300c0681000403028452005444500051041003690030060a80c41010b554150860300c602e84094110b400410a00c4013181d400350a242c152340e800c030f807a499040720682ca010040d100305c03204802c0e140140f0307048010407e0681c0c44036110b6030007070302598a42200c1040c04c0341190741c0c1114104050340c1610051140400c1c440b80c4034031175442080f0850a41400380c0004001c5441e0f42d02101380141400c5035042c042c10105100c00d580b17081804c03189500c0d41030441c00c5860b220f035081d5181c203c6980e14002003c507a002c002020718422404811036503032460f09802029403141030700556452188003408818200c003c0c04482c41030140e242c80391b0854988cd50200c0380703440c11a80c4140d26218000460025981c0d14030428000c501c2526102130071407043ca0807a05127805540308510491400c400c00000c1d98010820090100d03040320407106c03402d14003100300540c07940080780c0040c0840c240104410040b131200c0340b03074649281504980070720140740304000e0784000c0750 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 454100584 1250 454099334 454099337
    0x30b130201111204060e060f040b0409110915030403030f06081e030c0d1209051207140a03020304270507020d11060712020c011b08010f0b030903090f0a03050f030a0e0907 75
    0x40100f00a018030480c00c95039612002400645441c2c0100c1c00703581c289c5c01c01d80040c000300f400028100045486403040200718400200c1803800c00842000203400004002c00d820203040c800000142010f101e907004070a412145213041107040d03103070f03030100d980c40290f070828101e01043d29201c15060440001503c4480030480300405a0441c00c000c1204c4d115104150043c10030744902c10a800074400f400078124044883e1140c6480d42d0365420601100c10440315800f0300d9401a00d042004039902004945c180d50015401242c541120b460440d5440540c0c100c00c200a4907060a110904da4045018042c001e45642d80c1941004a03810041e240ca0068175040042174648903014040020340e00600020007081000181c84c010003a03510041402042820b00081c0c160300040c020a0080019079025100c540403890030f40c5885800c1954074803501d0748483c46100d00c0e1080034540d43c2c422650300003442d4030500707542810600c166015074907005802d0307a20205601c01b42c100c90901300480550b200311481e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 454101834 1250 454100584 454100587
    0x31303060902010207091a10050901080f06120109110316060e190b190f050717030c090a0e06090708092104050a03141209210304030b1302011112 64
    0x25996100c008100119049055000740d01c800038a107400c03442110505006003c0c101c003000300000c2049203003e0b00009100a1040500030b020841c6d0f030081200d0343c0301d0640e0342c3c1e2001c103031203040000311a140f04100315811076003801c05000800480c4000c5501080f4141c0803201013070203030a50703a00d082e40c040c01400c0004861200e030100d00e103070a803014802040000305c20444035445550b1450745501851031006401c0769101c954400c2c0c4d91006c906183c11400b407411700d041c441a03a80c0c1410020800c10304c046240c0011010a00314500a000c580d50004000d0202c00855a80d5062810f20041101d08030300c654081000503038241e0254111070311540d2004042c140b10301c2c3e4020000f42242440620001d622000d010118850f1121650000034500807280c48807030b6007940081503d02100d290010084000c20f0061080d50f403a090000e00c00701301d1139a1031607200070f100b030745180c41c50199501c054540340076401031008000d070840c07108030928002c0e62502c40e1400910300440c1d488000b4103020300580780 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 454103084 1250 454101834 454101839
    0x90705040305060a051e0a15050312042306040806010e15010e010f02010b1005070b091506010c212001062304090c0608091c02120306010302160b0106110313 69
    0x404d40c0021b501981000c500710313101814840341002c060f421100c207901140c0c0c6506247c1e080741003641280041000300c00a20722020103880042d42d50040b4840d00e4184010044e0911000e40794900815454202078005501e0f2b598a8512503500c860a2040b90681c18401d808100c56240c1c01031384003110700040c0c50707400c44825424011a008140c40030210110755072000c240183c0d071345180fa14540201550b40d180d803140302d1810103c40450001d45007450700c1d03224004041500d03034054500b5a202b07109003082c0051030b0a904080340000038101450712500d0242810510700358029420601c03d1010340586560601c3c260445822110603000d2050f03000981d5404218110900090a1710040054004508035406a035031a210030b0003500000081408402040890902001411006031401020b1200c00f0110720f4080c0d102c501c18150101c25140000c000340700f9034000e80490b00b011420200810401959082c1801200c000f80103260000300c07400b52401c8001070010a130b40811300c900c140b10407031a1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 454104334 1250 454103084 454103101
    0x7031a0907050d0f1b0e0f0d03051327090b0a02030a0204170c01020f0d210608030706090c080304051302180d060903090b03070519110a1109070504030506 68
    0x200007000c00741001003c111141161415015180300004003a0011400141c41401d0741c0c800c4020312000d80800225246442903691040e0800c0100d5106075400d055070007860804a82500c10f40d512050030140c030400008018120b03000713100d00c94410604038101111070584480c103503410040050b0503401500082b5126020940c011038015200aa0052074140d44403001481c0215a00c0ca09545400c80010380845580500084c12100e0f12000581a40364119a018080785100c0c8448d401144c01130418076542881c41d80408007501d00c460845c1c0c3c8651180c41c2980180201300012114605140c4000850b001c00009403025a00300134854400701e0b45644030078000350440100c1d5500d0745035407170707003000c0c4c51315032a20841003540500b10102c0ca1412904001e444040c0552004041c0101042004200c1d0352100651707000a2456040b080100120329003101d40440300140500c80e030203400c80b0001084000e210b520003188054030425810340d01c41340c0590b400c0c0541e10001e05181c2004c000a04d562 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 454105584 1250 454104334 454104349
    0x6041718040f06090903030b040b06030405031602060412123b04022208060606070b06010c02040b06160b180a0f0503120f0a0b030a081e09180f07031a 66
    0x10000d00d9030000345a5135404404d0300780d5a6130001640400e0382c6120940481c2080c1c050382e80d000809941092440c1800d507a5960740c1c2c030485e0400c12410380351049070301c115503c40d01102c009215205010588031028204a01d2451a441d442000318203002c482c41c02d0007034621168031213103039800902e03c2180c1d051590f841d00d45040b03140b4954003903030030070003442e41030ba98015007036440d2a44800c4800d010300f484074403032038941c000e80078034412502030001400117034041c0c494541c0301c038082c6816048021a0302c049000340542c0f02c40c10b5032100e804075084c21410000c451000c446800340c1542d88064540300c3c15100c445200d03401222058002e480018042903038a01040c005501c100d00701c9191020300c10010480810030351311080e40012038001d006521740d29001d142d4441400720041c050700000780c1e641031003c0c03244c00d82505079041d0021a08600c00420030640d409680c001d81603030700541800b030030801c001208440e9540105045004560400d10a20030700d609025145c0400321072207107031801c12055 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 454106834 1250 454105584 454105601
    0x90e0613020705010203150a06020c030303040609050a0c03060c09120c05060c100c0c0b09060601120513060203130530130302060d0f0b0f0a090905010b090106020604171804 76
    0x840d5020003902d400160240b00840c8180300041c041c500b103814500811109900503404502150311094048456540100860b600a948030000090481ca00d1411504040c41c8003006030201d88100c1001040c42402d41048a403d11030380d0b1030000850311250302030503500c2034490140004040c03110501c03043c1041c0f0300605011000c0c10440c6c81e4460401e260405980c10300c2d8501d400038042040400401c40e203d264140c1080444004e0010744c5804000200b418a280d00c02d401029100c60208514221a0030100300c1e05811001c295a40d207090151041c2e410f82c8200c04580c648248604111001554050748840c240b0004424000100015005265421800311f40340c1c440001100000141c0e0303000d009110090042e800420000c481c56000310031980c0c2011035078001d0b000f600c0000181e996074040003041c2c03442d10b607001038010380da424454010b20500000d55084050900046461070b000540c1c40d110b1881514101c104068450000480e400303010100d840300161060102c07201d10300703038100340c45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 454108084 1250 454106834 454106869
    0x41202030c090405030a02060117210c0d0804020a0e070507030c1a01080a110105040506070b0405031308070e0a150302010f11010204060f030b0d081c1b110d090e06 72
    0x140a40756800041240d10b09980443c0e1943c40011142e075172a030180041d41c01407408400c4640451018101c0c0380d111645015602268040d240d8511508520101517681d02e100325411524098441c84000c0c01c040e0040c4e4040c2d11840b00c445000800c549590f131203610a691641c2c403a42080d481c0d590584e082200464200d41c102c00006000c40c200480e4a0554002c05401004103200803c41c00c140703004118080030141040003c0005000607100c0310101c0f1080da03440b0b00d60640554407810500c0c01d40c081d81d0b4500900213140d61002070500c074000b03004000c1e42c6550440b16155150030589404072551a1003c0440250494007000958081c0d03251840071041c604140c13642e880031508050072070b40f00d9004030011400382460110102c0c2d141c0b107100440707402910224901c0055844000c000e014140c0a000d549401c030351081030703c08041d0810281018018850003052030081c02c098108180500b03d01028420000400c0030144100c605000b203d0150ba010402612040184090005810b24485 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 454109334 1250 454108084 454108093
    0xb041401050d0f141b040e0f060c0a0e0604030305090307080a030c08030712050c190e090a05062404030201030b041a0f0121050f070203070b16120c0801090e0d020304120203 76
    0x14441405e00c410902c20030103203d61041d042d0300d5000c12048030b00c043c15100306a41b111010140107680024096002000010780944858905600301c41016030708803510742000c0c02240000400d41c1290103041c60160440a0ba405c16441e000c440c0d40c0c0349800340c00503001400c0e00001001241180004681141a603d4040f14203091100014160369041c1d5100c2d40025000442c01c02c00d5204902c0c809074084a85005c4287c180e0340000211358140151000941903981c1000c22010b030380300f559001c0e100020120010740d01c0c002c1800000150014441640880c1c1000f0054000d464a4801c02d4107030800304080100314904c030000d1244030303a10010541d061040ca4000030840641c0c088810313004d5a05070402044902c0c008001c0d4141901c050044000d6500500c04000000c040c40c0b0402e6000d0b400480981002d8505107046508101401c0c800302110b190204502210740c0c4611074070705070340d85410203101005405841640d941d100155480c0181c02c24001405074140d40b100409a4500050455 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 454110584 1250 454109334 454109363
    0x105070605101401110303060631030606090501030f06200c0705100203070803180c12010c080108030910030b040b03010c23040e010509100b0d0b041401050d0f 70
    0x1116030030b5880c19004007011104200703400800208110202c1d00b0700c0c1510304c906112068a0b40c0780405012a4415103005ca0580c00000048003165400b03015009408484207400840c103030210200c0c001907070440d0401d0400310700c000160142c5c80c109ca034400200030004103561102c41c020403070f540c0c101806410702942d10a51207003003400ba140110224001d007041528000130003a2040700c0100507025074109222000110703a9500540703a004200130380c02c140302c91030002c01e80e041610840409500c030411b000340080c1d400055001241d107140c0e1f034540140e642d881d05401d5940e0f0003800100c56009006055040289120b50031908401d0341c05800811840d444c1c60000742945d402e041326100145254024070b810302e500201c61056060b10400d480e10f0302c4d0800203200340701c0205000b030301d0244850300049190110b0542070b01c0b00910503101196159005052040d0190415076001031040b0b060092000d0900800850b644c12240000d104225600d815039072502e40401c40c28090710000d1032075652 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 454111834 1250 454110584 454110593
    0x10204030b2a12251d0301090804030206030405030415030905061b03011e0807120c140a030204110c07061d090114010c031b050606040f1406011101062408090f0318010507 75
    0x5440ea814007980f1002e010301031002801e01700382c50705642213110b80e06254a0700003107608982101c0540b501a10240c0e5603680b03508089241d071066502c00c00c0803c10052071100700552540c07209080034400e0080e01c049803207508590480c00d0103410030019002c42080104100000c140101c210f4a4031207038a40d12841d958000d150905c60180c1c0103035010181c503501d403020080a400500d01034109210200384644000d40031030074400003070100900443d95107104001d8902c1d0041680c10144042c002c49000c2520f540c0020044040001c0388090141d000036498114605a80c1480c140d8114507200b130458000040119403550941e1425000d108e0250841f200350881005030b840c1c1c07039000700000c1c40f05061140c240001c44644005c0c00d103034240f81007000d600c000200c1c00c480e03400c04400d190946034000c485800500408950780541524181c1180aa02031240400741c00c1000c051611206096510f4104244e00c603440360310228816002080900c1c0021644160401c8030b0406240003414182c55a84 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 454113084 1250 454111834 454111891
    0x51003050a050f060612190204020403080315031e0a061a060a170a0209011b0c120309030203010b06160b1b0c0102071506060c060b060c010204030b2a12 67
    0x42e50a82c1140c580003c03800820000141c014400741d420402c002c0d18501030315103c000c4100b00520956000c1c15800641d919a016500952781105006681381445000424030014601c032850007805140e0700189080400240001d5802c11800940302c41c90850355060014960000b60b4200286401380001254407840007070424104075407121084400700e02205c480300040100340e10340003801041004082c1c0d0303000c90344e45d6828030078240c0d0500200b607074030384070b01164419000105007030429070014081c1544000c040007124002c0d4003c22132900002c0500c40180306000004610461101d000b83c001402020a0350788003d05041c0000440c00240c074010b40c070351140e0004c0d00711b60b4002c9265002c0c0403100c20f9942080c01c0050b0104440c0b4a03080f8003610190012901074949952098450b09640b6164200c0340240e0002008545e07c5880c0e1030a904920803d58030a0000c003019000240c503980c40076488440d042408079040d00f803c0c0014980b6580c503900a0600380f4800482490310340c030400819 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 454114334 1250 454113084 454113103
    0x1a10032016052a030a031409010c080d0c17090723030a03090312022b0c050601090c11070803090d020f040e10150b09040e0f12070210030b031005100305 67
    0x1601c80741d03010f040c0d5900c107409103021200a10a07081809a400025005031481c89414182001d01c2d84a0410344010707160050b8011000e801100001a590411010780e44651b4804000f030711983d07400480c00c004500c5d07011044500c04281c0c0d002607070900290803851940c800160001c00301c82c40d08031b4181c02190610190345000c40100d0341c080b5051042080024194904401c2803000305800001c0d8925980000c00c6039150505000d03202105240283c411074000099540117000c130b03240b0b565035140781c400510f4040318180c009a04155401c09503440840c000c001c450442000f1814600b20100300311030310606100c1240e00c00f520504802c0c2d0340d100c1d40901d01c810801c02e406004050410ba40903070544042d03140c0c04558006030001402940400800d1310040c09050328006800d0684280d5185000028131700f900403841000c0b040301c1e00401c1c80000f81240c500c00c0d10328150710481c500c010b030103440744052915416002684100c0c01c91005501580c0d10000680007020f155640e40c891504005101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 454115584 1250 454114334 454114363
    0x4080a112107020f030105100303110705150a0212130315021b07051f2304080601080303041209030803041410020d0905010b01090605070813091a1003201605 69
    0x41100c02c19443c202c0b25180e031054003035000340709605e0007040d4080142e01d1404010701744403d8108907266444e040124070003030721001e00f9001448028070700302d40041e00a8000038006102c1c1070301c0341c203050031103c050380c0000c0c01902e40e40907020f045a8846e040d40b046039001031103d543c01d02400c660340203c0e1415015179031030140600b0301242030605101054030f810031420583e100c1032400c100c415a010026040070003241d0000240040d40014402c00c0344034517031102c0c0007845041d0003c200c202000c4001c50142c1e00c40c0b240c8011100040c00305692140c0b9921000c0c10240c001c0c00004c011514920310420300c07050280c182c3d040300d60070100c01400c913080a00d01c140100d03516651034007017040034810400514004d08050009a04c2c00b24001c103584102d0f080200040b00c081a600500001a5045d2010309507021081c0606204c002c0501589a0984000d51054989188074508035004c2c2c406c2401880d140b12002010100450280c003e943c0403408502c40542031071103403004118184001444124031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 454116834 1250 454115584 454115587
    0x1031119080a0e0a14101b080a0c0f0e031204060c0201140708042102100c12031a01031d030f0301080f0304080c100e09040602130e04080a1121 63
    0x20918000c2401c400202039144031450b21242030b4031001e0008194040c00d601aa0b00a090b03c0c41d40340142c1810300314030b04800e856003002a50603e4420900ea00d402c0404030303036100d030210380c0d9820081c8140c5007117800341004655041c103590100e038031840703900304c10b140050103c1d40b0f0300746600081290342d8800d92000b80014011300c103100171903a108015000c0030740501c10030740c140103541d01c1e4103030103102da84503020207107050703105601090300c00004407450320303070010b041e00035081105001804003c3c20310021070300f48181c071150701d1819000e80314840480000311100142c0b808800e005500030b18501800c2d0703580c294403c0504051007004c100078a0032143d20005203460703525080b20945081480d1000413070540040c4800d10421100003041000988119080441c44d0701e900000da4858014035101600160000200f005101c40c5070004d1810940c9030202070003941c0d840e24100c0d10b5040603180100519020000035115a05c03529017210006d2280b029600c002105184030740d4502c0c02d540900811450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 454118084 1250 454116834 454116877
    0x1f031e14010c110f060708100806041a06270c1c0603060615080604020d06051c210206060409051203011806330509100203040f120507030b06010311 65
    0xd003d60603202d00c100400042500d01036904e043c3d170315080700510203800c0028002c00aa014550501042d00810301c44041c0c0c1c1481c281801c086189501071002102481e4130381000c03d101c0d0a080210001034404030041e01d1542c07040358450785400fa8042d1003103401807000e00004401140e41000c0c4c500031680004002000c501d140b03007070300c01e59826500c48194528443c20700a106508401c0b0b05900c508200d50040e5148002d032920300003040d1a800c20368201e5075100c0349440d01090385d0f070100394640c016036042e5000f001a18403140e80c031041251150050300250301280300c40c1040d401440030140300300e0541d0310004240088c1c2c10035802c26440725080014105900031022051f01c2924050500c4100040400c5440305800e101e05200da1130000700c280e5001180548588110300392041102c0080495240d441885c200940e2078000e400b510140c07000082e0002605402502c0222120307a02401410210345503440380c0081c0c40f00201482c1c1819265500d00b92490320200080016000003600100c2042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 454119334 1250 454118084 454118087
    0xb1510020a0516030804270e010f050105040e030409020c03120705071506050f0f28140a0e060613030f0602030106020c010f140901030b04020309060402091f031e14010c 74
    0x5240007aa000b40100103c05201041d4903204480c140c41c10510007040a9a0440004040806081509010300e20340080d885110006400074002c0f050b0741142408186d80380c004110885400310000d541a0780208401c00c4250740036005000c4e0300c0382c5001a0390a0032310141d0a043d800c501201e030103002400005030350301080404603c0700c0381c210f120042001902c0c140008207180c4071070808090b105000380c107407140007035580c0c5810405d400c0c900300106034a034406d280b01072840c1c04607016042c0150041c02104070f0a04000340000c00f11410421828000c0e12044240035042d401030202c81c0c04100d981c6800700100d814100c800850b14840c200050780c07903141c284000d0610103d00700c810304000307034030f41c0c032013003d40d030204d0300b100492141c84840303585800c0c0070016801014400b0305160064000320030071244400202ea0544900e0098a020801d0340d100f0311002c02e0b03c004d0001d19990382c1c1034454188045000c00300c2c080e90610052800d420050103585a0700c491035502d03401009507070344030390b00290303101d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 454120584 1250 454119334 454119343
    0x406140910090806100f14130c020708070506070807060b060c010203090d030e0d08040803070302041e05040b0324070921060605010e0105121b0c0102040f0e01120b1510020a05 77
    0x45c2039802c2c0c4000142402c2207511180c0680c0300b10018088203c2e02101c4a90310040488507000003c02c08102013100c44c1d001a407103950130302c0313a44880e0140781d90010382030410108494209510008a81c03030320300c0990b134110050080e6181c0a4206200f84802d10880c44240300a6010381e078034070003e141444202200505607000400400c0043d0051040e8088540e0040700f625042944418801d80740d03640c141088001b4080c8e60b000c0c4485082041507811000c620f4803828080e00d0080d2024081c46003210181a07880011010304119141c0010f0710344450165904810741000032383ca80125600c0e503900d2849038000c0c541912441914031800f844041062034803030320008100030308100e031256281c0400070340a80205000d02c01561450380c001031159039001107001d0341902c0305040584800540d070341c050007504940100742100f5040400810b6820680c4c20f00c9049510b004c4091603582c10550b80c491084002030104400b4002c84c0030451000e42c3e800502e1392585620f60f0040801200341c0c2045440c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 454121834 1250 454120584 454120591
    0x301031a1b0a120b10050405040c0e03120a020c0607060f0501061b080318030f0c010b0604270b0a17060f07020c12210d0b04060503030406140910090806 67
    0x1030024002040c1c400380c103070740d0648100080c50305080304550403000901002d401030399070350b41e03001d081105040d010320703004000382040e00c0c4241c40401c440114050141c40c104d6558000e91fa056102d00036104801c0701040003071a20f00c0700340c07055803800d142c080d022640c5900210400c54929458a0b460310350705c01d1910940d80140f010b071800b12620b90040c0008040d00a80746801f50402c1d00000024981c030500070862401e0140e032808803550b41d0002403960525800c03c1260349901e508140c54000c1da4540b080545003550f0086541c641075621490381d8650102190101000f025190851100c1d2a624081080700414240140306036041e041024641015030040c0240741e20840d20041c44884c0c0d90000700078101c4881541e444003042d60600b201440c050b900141070396070036010ad038a400701da8481000340046040d542c6060000c0340c64034041005031103032030007890742543c8240000c0004502c100090f019009042300e0b41450041c2c21b1010400c03002d648640000490403031b000403c1086404c205d220b50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 454123084 1250 454121834 454121851
    0x30d14220209070323070c051b0a0501080a0e010606020f0d030908160c1a09090c030f2a0d0902030c0a0b0901050901030216050601030312230c0405060301031a 70
    0x152080c540e80040c40c50400030340758000301039540c01440001440f00f0080161012003907110f500902e04036000500328851000200c0d1a8003074620030070013410140203130740542c05004181405840c1031000441d01440010322910b409501c601c035007544c440c001c2c030805016081550262510328000c3d1401807800084424035400c0501c0e28135020082070500080d10441401c540908034849481d08000b026136009030400d20103c20800414410844900b0007425504400d5561441d185da070312a01c010140402c840807a4502c162400256480c2d800c41076809518943e40c01d03038100c4002c824040b103010b801507004d004100359201c00749029403604000c1c000d4410803c683c01c0c2610350400e80d82c90114005c1070090f034140302010070b1200c0c4607030082c1c0583d2908006d0034074500b5102c8050038100c2c0c1d110028402640458120740600410a000d4050107003c900442001c1196016440303002400c810001d0440060880500012541c4e40e900300040d4021030190501441e4403c0e4200c609041c1c40014001c0e95 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 454124334 1250 454123084 454123141
    0x41e080624011b050705120c010903150e1f0f0902060306040b150f0403060605040b0a06080402041d011b030b010512091c0f0905040b010801060e0f0306070908120921030d14 76
    0x8c240c1c4e204061006407507020080300b44818500b031480001c0c1288241c41d1b0300902640c441009001800c4542800c802c1e5005414440c0703281d540751210403142d000d50045c1d0001d00800c00141a82000d0700515900300d03002e0036103011140c5000444040e80c21598902e550540300080420a0013200e02034040a41002c070303003c20021071407100191070f420b618840d050034403f0003000541959541c2d8403902c2444200765404034030941800d4014005c0039691410640c0c0801c840c00155060f110344202610000103866440c5449103801c07000380b20800c01050361059105e81308078500140c04030b2500e900c0240058581d001200c8203940c024055800c141c00c018011440d05030059166a440800981114134504110b1200043d00010070200c0c80244220342d0944103031000d00c10629803094540003124245000d66400c112a000c01d030a0f10301c2064003040e800b001d00b01c0282d00000c1041e000c6481201e0600c1182d1506001044001c00d541d2800c2c0350309401d8842004000c00c062249900a80381c00d00c0343c00c050f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 454125584 1250 454124334 454124353
    0x10803221202010f020c040207061e110904020904060924061106180a02040c050d0b04181e0506040c03030e01020d090b1608041e080624011b05070512 66
    0x120202100040d001c3e04019951241220003402440031280b1444041d0003556510050308180d8041d00303800c1e800c0841d0010b10745410b03401ca00c2500c1417444203e440c0c2c8481c0d252212400400003c5e411200c440d5600680e5094001409643c52158210f45c0e10b03102030144e8490b61218100603140d420740e000c6c1003440704018604009100105115901501c098882103118407802500c0f49465030050009421030b02c2d03c0c004854994101c009080703d4520302c4030078465010b008040c00140c840301c402d00c110141700b411118002445100200510300c035080070480b64443c00c2e07140c0e10700d4040183c8054406080040d014018950b00c01035581d00d43d8001e000030910700d58900001001510b2a100d280050600800c60300f0488481c05981c1c2642604048203603240c82e00d4804c50740c0103006d00390459400405080300086d8050010500c00e105e109000404422182032268000704141c54070300c881e040161414000070f0091602110001c078501540007040d0b8a8144010b00070301144a500103545a40b0070b0103031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 454126834 1250 454125584 454125599
    0x6060f0b040b0a030207142505010f020c06210f0615030c031f0503070f14010306120803070c060c11012702010e03100c0206040516031221020301080322 67
    0x1110740d50b080740e01d40107a0b20086030a020500140103222603085015210840440200b42001d208c110f0b1421000004c00550341d03001952066005200c400141e00401d103040c0003481d03c4d4000e8006079140c1030107100805004412080c58030400c80b401c171a41d000500c18001ca40c10800000750002c0982c413010381c59414261502c19841c00f0042804082c500d10100d5148421407003071014008120140440300c0141c2c032010b550b10541842c3c0624441c01001d01c06042843d0310074001c80084135001d500c5000c411001b6290305031180d00091500017406071081c4d4540008229108992300c0600d00c2c0d44661030522400801429100001c0c2101c40e84c0c0004038085001361800c6882e41049642424408d0002004d00c020a041401510b5002d501d036141c0741c0142902c035000301c2c0070740c803680c4103405407084101c102070507a1841d03d17280006405000380c0481038201c140911240d0503a036890710601c401c0303c009041400d0a9038401d81101016030000b14520b46851001200c1d0742d800c4d940c4402e0b003810300d8100b000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 454128084 1250 454126834 454126837
    0x30f0908030c0306030111030c041703040b04150c05070e07032d09060b03010e0106060f0507050309040e0a0f11040b031504061d160f08010b01080c0c010e030706060f0b040b 76
    0x10342c0c62a40d81c000041003580d03800b5131150303602c1c440714403009032240391412140030340d504584640d005444801d034022000c0326001c4225010f450300310801d982000d0800380036003100c69100110800303108618400c84045681000408010041c000c0e00102c2c0703140042004090341d900751840c2034a5081d00301270402031189103411444044001d90b0005040f08a800d185016002400400b5010b5180420304448014107401000540e601600c44403402d980100c4111901d2145d035002070904d42023844a5001403905400629980c1030440071505525080d44403519400c4401008460b141c08000030740306581040d0103030000401d000c8001e0501620064680b038480c00c0010b10081c403040d61565411440310380e081c207c84211100000312680080c0165482c01038100c207000b00304070304030302480001c1c1c1a541400748982001042c1c3d22040141c45002c02072030030f9048031000314929504c846032000d074100100058283c82d800b884010803c14500119281c2c03d1201750824254008100001d100c101c05210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 454129334 1250 454128084 454128091
    0x100503130311070e1f05240a0228030e01080c070b0613020a030e060a020a090e070908100c02060c07020315090f15060a120209041b050d03020a030e0f0a091109061603030f090803 78
    0x1031107a0b1010b074003c02720f00309451050441c143c02d00322520144400901138024150a104c6e0300c4629080b0103040054545440c220f40401e1441d404020b03442c001030326460510380103072000d880243c51142500f1103000366001017061800086e40c480800300c60060401843d070308203c2076002140b40140340d2100400c0b005c00e82c0a0030044040031310124a03464441d161ba10000c1c203130b5105a80d01c1400c0881004054030988249000501c1210089400010000c2c1110a0240c0c014024041c6280c01c0c400785150020080540c1250b00130207940c40d9510b0020b108030003040c00c45022603062881c0080c00c01c20a0b42190304100403901e0810712000050300c900382a5900300d81c020683e00403000c0b0803100002c10701410341020b40c02040c644215810150001000c0b154a44070351640890384548c4014468000e5031040b4a0b6070080786510700701700420040e8000740004000c65205803030210300303901041d5075138004c4d44480f9003e45d860940c50b040c168544200d00c03100305070b4182800b0300040307615580203e00024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 454130584 1250 454129334 454129399
    0xe0708090706082a160f06050c030c1219050a060816030c18090f1118040314090604030606030309030c0b0a08151306090605100503130311070e1f05 65
    0x540c074030411601362001d450312490020762444030301449150182d0076075841e41c01200d000342007001060f0f42d800c00d00305991182400340482c900300707403c07660554100d440140161492441261814249101900650b8440c44600f2070200c0c2e40c516200b140d503d050311020901951101825007400007965003041321007202c4080c04000d01c1310211251003c010070700040300400c43c5031841c800208102c4400c601301090b000484000310182460220101076142c00c540042c0021b2880310340301e00c0b44800001401c440c44000c1c2002e424507403030b903441004403002d1382c00503004110210790400801c405165640060640100d4031424201c921002911905014114078503042000f0340002d03641d118800145840d15407010184a40c40c0c5c6c40d6107034001865940112405102c074694001078082c020b00071a0701508c80e0411200580c2106c0e1000c803414810303002c0400b00d9014028001404125074941d4900610120750383e1003502480100035115401c1e1a40098060f079140d03038100068941c00d14010b401c0c803900c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 454131834 1250 454130584 454130641
    0x2f09160e011701050118151d010302070b0606180303072109080c1c050102031614040b0403060b04020c1b040507030e0a120207150e0a0608100308130e070809070608 72
    0x3041101101d650b5805c03421441101d00c002e03018060723000303481c03240400200d00340c01184d00e0250300440c01d03403040c2c05002e4402c0002001090712400d02400406912011092030b8002000040000b0308560140c0070030340d4000d80102180310f1545043c2c1220f40643c110b81040421185094101070f01c5501c4c800145102c0d4002421242140090320415407803258000021544e80c60285920881010680001d034009403c1b000482c224000c4407085400b541c0e9030b601c0f100c3c14640b8641d100b00160a100c0d00254009400340304048040108114008809500e0b10614280c1500c000912040b00c00c0200104209030400d007160704050790201e030800c481600510540b20300445078800743c2c0b90003480d90016078038450ba8813020018542c88681c240f0080001c0311002c640940d204401c50340c4081c19600313140011441d2400304005412100100706040050454044039a07441c4620f0121900441c5d104011a200f10b04000c4240401c0c4a00000340c620350400f05001e0030300d00700101d11407668103c440080c084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 454133084 1250 454131834 454131857
    0x60d0f050c10021c02010204061706031c090303080a0b010c03031812020307020a0b0307081602010f0606050c061305030f0a0908031603020f0601032f09160e0117010501 74
    0x1414003520100344000b074040034041600600095a500722000107414001c0400c3c0120072042c410b0007100c00f107035540d5586421006600203204641040540450b60510445001e00c00802090220110036140c54580003015482d6043c007801036080104410707001450071610103810703030f0810f2040703400760741500d00054201006c0256204041e080100681242000d03000ca07201158000020b0a03418801e0716540c4100d5943c148010850000b500c0c49000b0908400000f08a504600b21520480c0c0042c0300104204004801800491300c003a004100080c0d13000803c46081c51040040d40d40040c141c3c4150a0380a882d516000d80320b001d80c010b844045140040d103911300521400800025140050a480e500c102c040c06080e6082c1040c6d8086000d4012081e00d40d40e18000030803018100c03a0000025400703030254100c004c2e01d800900c6c82c46801d80300c03a0400d176805030300d400311741c0c03413041c540d40c058070540c0112004041c00e001204100681004107091580104464003120941110400c0c20005803003503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 454134334 1250 454133084 454133093
    0x40204090c03060b031b030a0311031201090615050a02070915051206090c0a03030905090415021803070f21020301090f0c03020f01080705030f091e0c040f05060d0f 72
    0x16905801400500a481c4040b042c0062640500000c541c21400c452800281c41417018000215403009607150304803021030408203009401030441803084006883c03804460004881002c03d082e0880c07404655100401c1c03240440c1d84259008510007810500c0c03c2000000000b5910442400b0340d01030140c40f01800c68888a411144801510000303000030741105c41004000d40d62441294885054801d003240c801403400c00100c22010799070581e407881c00240c18031040c08807024000e081220140e42000780103c900d0b00e50302c00741c2800c10546441c050825a40e000b01071920030366400400100c89400c6003003042c00080382c0d101c0703e460300c4040c07480d81e60712881c000640100144200600845000c1c004a8100803d001da6541940c2c800c41d445104419000d0045403140e5007110140d020070800c2010400081100b0301c060b610117940c50866907050110000c042270700e440710540400d01c0c2c2c04a41c108010b8139103405800304851003602c08000900c0c088001400440d40c0610252182a03001100000c5c403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 454135584 1250 454134334 454134341
    0x40b0a0b04023a060303231314030d1b0f02062b06080604030c06200a020307050709090f1202010f150905060f031c050d0e03040e01060302041a03040204 67
    0x141d0703062502c514100610b20340d020203e840c0c150200041c4504088180c000b10134426481900d405566400011141000340b0b203c0c604458165140e1000c1409007480d1711021900c0540500003a074607040201c02d0050901d80340055040c07143d4180301200403040c076100a80c0030400170881d0845400c00c3c489502c2d00104030a8800c81803106d00c4984449203840700000c100d0f0f98240e20240080c000c014469a50507910b403a51002d5070020b0000310a13400d0080858855004813546200000102810484004006000c0c1c0c6c442000c88015810208200040c0001444030f4001081103501c180f0007085607940e00f5108006809008007140044011440d015100358070005d0a0b000300d01d010406404d0003041c01440b50540d1068000c42800c2200113120740c18074064913014000040c000303094000b100004c000d40072500d503007900100030b014800b6a0b000e012030300542c1507111001c00615070b02c500300710103c81c4005050b005a0245401003104210115030202150741009076819469229240ca100242c0503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 454136690 1106 454135584 454135597
    0x7060305191e0f110d021b01180209160c02061b0613021f080109050a0f020c10060f03020a0b0304020d0f06050403020c09040b0a0b0402 60
    0x419000350046500214260060401010041901002ca4208110a010508909100d2007401205100c0c1940021003107000b4841c0c4d59800441008134810401031000069002500c00d500310030300c510b851842010b14009201900d40076240011100c0c03044001ea120345003800100781c1e41c01031412181128052a2500006003030a9004c0160a400840080c1d0382d12290220040840c9014003107140300e404c10a0545944410030f00510000e0a0415000803008203081009a8148d412800e040d044495091001c900b035900c019040307020788400e40c0b4008070f5a0012440020460011402c2040e2414504040002c1c581d10001d6030003d402e10300c4080e420890a60302400901c403108011640280040c0070b210781c80b5000d6848240396034030600c0944039030b40d8074420712040590500c22a10312030b82c05c4805054900303098480606078000035141c4481b240e503440c041c409903120303501030b01c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 453956834 454136690 := by
  have h0 := BRFrame.cov_init 453956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 453956834 ≤ n) (h2 : n < 454136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
