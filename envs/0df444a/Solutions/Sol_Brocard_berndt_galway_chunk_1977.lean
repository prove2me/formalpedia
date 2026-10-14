-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1977
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:22:12.688973+00:00
-- url     : https://prove2.me/submissions/46eaed8e-025d-44d9-950e-aeca12dcb403

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 355395683 ≤ n < 355575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 355396933 1250 355395683 355395697
    0x100504030207150306050411041214070f06021606051806091201062402030403021309030314070512010e010b250605010906030201030e010e07050d080c030409022508030f0408 77
    0x30803034055401110f0013800b81c240741c03140c80d02642c60316000510018800c1d0803130b41641d00480341c042011015035100c201001d8166202d00643c00344c0700300400c144103001d65140040c481c9078000c10080200002c8026000e01c168060005d00c20b0401811007203a0074442c80030440801200c000c0e48030300004001c209103e0644201c41c006510b03040000c81c0280c4050800440301041d00c458103103550a40300207903a02d11a03404082e5002e820000303400300b4071132a9003088600034424500864058110601420b00000584900001ca034000c00c1c81c201d81603d44a900e4014404201082e446500d4002c0014a500c509418a10f041490040f002038090005214020b900d510000402c200d6940d11002401070200c0d0008900182c01c01849d104000c10500400c15480c09090242246a1600041103070040170200c04844c1020103110541c645502070001e08014400d079080965500840001001078002404c280d8110070030401d022800715080000366940400d554591002644490800d64694003c0c52 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 355398183 1250 355396933 355396949
    0x1050714030c070303181a030c07021201020a030b010c0c061103040f03050c1f2007050402030f0604050601020304030309330207080c010e1305070c0b04060506150c100504030207 78
    0x8180b040b814001558008480c0242d44503825911a86c8049162454074070405400d4881c40034020713104401c20780219042a41011110f00d0100940d0104007819030340c6405070041d0b540407922911440d058041c00f03580c94003d29203640c40b08074540d034048442c0d851340128020068490041004070000b00100c8000c0d09241001c40e91090382c80c901503a403202d1945042d4018100e0204510316052a03c02c1c40d00c00c90352545900882d1058040c41c40710400400c40c28803001e118071000050251070b00c1c4020740c00341000c59501100786c5840c100380801d072100070300030350304550081200f040440c2e0710080900070b86480d1b14074003503890740b4951240e040d1850249244180341d180c072580f15216400050b02030468040034199219030f84070350015909a075200030400e810100b60091694031121550007207900c07102500341080c5c0c02038184c4070b21401c02030440b011107007940c1e00c0c0d040c401c007031505a80d288110401c0c00301c2580703042407103041d094803a280c0041c0d00d5003551311100401c08142c001e11605024001c80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 355399433 1250 355398183 355398187
    0x405250f030f111c150615111903030f0c020703021507050a0c151206050d080f04030b01121110050405090721020a030f0e0a0215040e16110a020f0105071403 69
    0x13030910070010801d504002c0720b04140c1c404d83c1c5240100c2c0c500400c070032500c0300040c081c84a283e4041c203840762408056540a036010305d6848109050030000c0800c180e0707000b5a8005108000006500112206185c010040d58402c0343d003000140d41e0f100e1126510302e840942103441c2d03110741c500140341070782d030381002090b110307a124000c01d5008560341200070b121000e590f4113018050186034101183c00b41d02680343c05c514120342c6000456810b0340141400386d440c421283c07420340d4039118609812000c2c1c00241071001e50090315804c0c00004070030310000404c03c03204018508460b05020b01944214030445001d0320448000586560003a201d4104d101c0000c0180b44c2c510455030700400095001c08082000f00341b40c00d8071800391080c9440307010200a5400d006091845041e001c10813007208501ca03000752070004020110b00b0740c014402481c040c0c2c8502d00d0380003500301072035000b030301000c0e010201d9600c0380d00468100001d81d4a00004a040e80800e09240d07645a1841c1004420842c3d61080354950b4480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 355400683 1250 355399433 355399459
    0x31b120c0b070903020f061c110a0809060f040f0f02040c0809071a040b091302040320120c1509091303021203070203090910030501050405250f030f11 66
    0x41012121284078001054495564400645a201c030300d00000e504082c081c0b560000d9030404000404400c50902038900c2800520030000c030507200e61500f01c0c4e272000c5000c203000708001d41052030316400682d014050400c0d8900340102d503000030030084c00500b2a1995841100a20002c0c4903040e007190340142081c001042484400750081109441300d1102c1d100e54680021b80c5001c120072a610030461200e41c902c2e0610b030030141f04041e00f200a11650000707402807a07c4005000380300500c0203611071100c207e09000311314090031000d100f02224901410150103132141c0d9003004600c00d441100c0441d42c114030210411009221801000003403600803002d08240104020000c0c0004034440c03207a82112803d1041101c1c0c034070070340000c0d81c044015a0007030240c1ca01501e842940c03a5400b403c07036031944100940ea03445040c20341d00191030640c0d1079000304400000780d4602140d2008104540d000384800d49140000003059000d041c0700203020940d20090301010480043d101c1c840d6118028404a50742030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 355401933 1250 355400683 355400687
    0x20904090c0e09030703080f090c1011070504020328060b070605011404140a0c0215041208060f01020a0f30030c0906080f092a01020c040603080403031b12 68
    0x20391070003101e001d00300e0540000c5088800104172550f0f580e1507a43c008540e202c00140003482d400203004a602401584040403c64443c029079081d03610b032643e1642198250440324605200443d044113019500400c03c00600d001c070004214000007050703d144005080528030300005060076080114030b9000080c544081c0322107074100506841c1841e0040200c0e00c0540200300c100d40c0307184078410010003000002a10000d140d03210040e200342a0045d240210396007070890100c50300c201c034201c4a50154100001c43c0d191f022034010760240003a9645480c40d81c2d4200081d641c0c00e01c1200041c40c0c01594055881000950a055409420380402040650b400c1c040200d240007803000c40240004e1402640070201032040e85220110780c03698480c0344007904d990804110140c001440340e00544030740e401c900c180d00342c061240050144108081180c20118100080c01c2a400e241d1551080d030506c0c0051011410303200448084981c5410040e0500612803aa91700c8140c0501d4098034030300c0300ea0000280b179a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 355403183 1250 355401933 355401953
    0x30e0a080d031109091303090e13050606030601081b04060302030a11010212040b0d0513050604110a17101d070905011805041203050702010b090c0409050f070e1302090409 75
    0x120341502c092040e20021038980c0694007484000740d5003c02000c0c00304010810040300c0d44101402803078000c0c102c90301c503c40d821000500707844080f48503c050019a060010a000c0c054115804401400c199450040e20f070f5940c20b035824002004001200c04081c541c1d440341e00c10740086a0280903600642c07000c2c10400a075070135000c8424094020203801a401500302402c40301039a612901003420440b88040c504000d00008124101082c000b81610000c60010000284598411084d000b4030301c22100910141161301d07801400b209003100076800f1103110101d030030a09005680400109105118100101041030180324071440c0a04003001c661540d0b1a00154161006940030341c40403c1082d900f01d0484804903405401030070303078a0b207020700503120303030031040d00103003180b00214040b5000c4002410300c200680d004c2c0d0801e5000501040500c9550066a0340030142c2003008030b25181180380540118442207030144140f58003006441c0800c825815600c40d05402341041020054605d060f00600c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 355404433 1250 355403183 355403203
    0x5010203070e031912051611042003010905100b070804060323061306090c05070506060303070b13030302121f0f1d040c0e160807020d0807050304030e0a08 68
    0x8010000350511420000303040c00b5180b40058081008004a403165202610305c040540c0410404100d0404000d00d5a0180b000c001d015250090100200b10100b0086503a070059840304004041c0e40300e42c10b2410710341620304403030080002046503070316200c0304501c001580e003144654901c0803a12505010025001d0815241300380c40401c0b03404890a01c0b005207240203204450600219000a0b0701c80c146590300000c21038600c0008542180c50740e007024141d0b4042e29141001500100b0044140041000003c0c0c005c0c009078090f52030103080c1c4d00d1b0545001d1b070040c5130840210b0510501000c041c46941190540072026180401504080c0240d078100d001c807069841c000821a540030500710402480c407021a0807800340b44485030347c001200d10340700074001e00c141c801e4000041c0001300003c40d40020b510400c110041d01410080701ca0015210170310160000707086500c440c00211007140c219014a4204149046c131680b170340c0d141e24080b201035805038412904142011310004006100256170741c1e40d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 355405683 1250 355404433 355404437
    0x40e0613140a0b0c0c160513020a0e0301230f040507030314190309290114120a0c1703030708041e0f0503031603050f07050c150c0d0b0103020c0a020424030501020307 73
    0x25401e6110041d400ca4015002c7d03075603c216852000b65143d9415801001c07481468180741084a28010000b42100c3d850315018000c04866141c91409480701843c00351311a81c0c50b45088114101529510341e5050720740001818403440200050111040005858034043c000c44003481001702404018007030301d1100000c4828031122900803100c0790500d9081504003005a82c0f50801e68a88145410007000301540142c0100c01004071030614401480b220f0032041c010020052981d281c0440314021540180d8401e000b030b00148240154540c0c00903180ba0015002020030070b5945480fa070503d030035941480c3c0100300f40700d0584080d08001c000b0000c3c3d4400c00910343d0399030341c520fa508001c1c0c091b40c00441d0b4044841071407900040115000c1c0003e010307006170600c115030100c90820030080f0781020546e081801031902240741c42d00381d038007405035482400c2c0a03e03041d400c0c044810350440d591480c804000b4410707510b403000240b40702c40b1000040c4032181c03001c207400145580c03414503d00079401545c142c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 355406933 1250 355405683 355405693
    0x5010f06120209033309011401060c05030406030c1202130e06010c030e10170c0913060e04030c020613090b09010501140d02031e15040e0613140a0b0c0c 67
    0x14840c0410b200f40d980c4914050060556144941402c2c040b1040d4a4800c0c0b4045200d00c2d0a281003540003007070305104542440c000a5102c4611086034802c0728143c3c04001040490107142d4000350700030095504440c02d904000c181005100300960741c2540070525a6035040c4003140d40440304500b45041d00440e1000c00b008000d03900d90100440f04520300b0007010300450001e100e54055401d20404000c103244480c0303058a1243c0303001011075498001695088494140490f022000d45440050220b1103100000100201d51a040c4040e45d041c400038006001d10042007004019900e480084030640b080c000b01040d100d5446050f604000c04480042d240140c80000000c68154021072800c4025a0460002d1b0708050350800c0c2c074070281d40000d0184c0e01015543e694440388103014042640a00c5410300c1c50f1078103079645414041224000078100030f00b9030048007445070341b000b00100e0401058020b24049080110321882c10300c0e09003040002448503c808040107190f41d840c501414582c2c0514007aa0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 355408183 1250 355406933 355406957
    0x100e072112090b1b19050a1b060816030605030607030609050f09070e0703060905070818061012060603020901090212011a030f0403031806021305041b0309031205010f06 74
    0x16202c030250700a0f21036040c000c000082920b81e50703540f2108401c000744219040d0010190801013002d04075403040700c4541c00344480038100541d003c4d00307400500f000940840010320701400201144c0010f46043c41803021446149007241c4a50001c00140202a00b12402e6003403580c0014000c1185204203c0b20a1401c404120980f8141f52030901a10501c1c00030421242404480d00740d00e0000750106080c1a694200050303007000301d0107107511820701502d80e0240b5240c208400c189041d054144800c881e0403000030080304001ca80b240c401607c11200b03510343c94141a2411400a24090300041d5100c1b00400000541d508550010424960001c0510660f42d90b40d500a542104080f255016102000d000080c0384024001034550301c00d0007403501085071108151071b080060340001c0140c601a03000542000d0034414405024001c1c02c003500c00b0402c500740c440071950320f90f1300b694100301050344881c89181810300c161325610581c0d03402c540820031941d692144074418810b80c80f809000c03d00b007014031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 355409433 1250 355408183 355408187
    0x110702030f1c05130b030612010908070b0c090a0621050c0a02010c0206010e04020607060b0d0609030912080702040903021c0905010e090c19111203090f0609100e072112 74
    0x130710050071914100f6554203040c0b0b012400150402081540c220000c03105150100409000700710740382d4007840280741c3d40c40082c1803402240034020000d40e0380c0c8004000350845621948044011100e540c942100d0700c4c00d07105004410b418403510940031003400c2c0000e1121004406000309a0599160020070124507914030982e11460244188005200400c0001e40541020390080c0b1000c0c1c4191030000d56030741194001000c8403544030040e00d54698607681c0c10105504010304c503024041c580c1c1458080c851668500510b4880d0b40e034028000c0d0b80b210b0030001018000c0004407a04001c40030322640111440310002c0c030106a510540d40092052649203141d8100713008128002c41d0348c1d2417402d00d0274071008000251000c3c868034080420680401d0305200120501c40f408041c0401b8501540c1c9083c40560f0b40d1502641c802c0724540c58000000388000544000f9201401c02c8614002040b540c0003032a501e0308042107684102604e0140f955150140491441e0b40c011841c403656924040d50410081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 355410683 1250 355409433 355409437
    0xd02040b06040305010e0c2b080d020703050304061401082802030f0a1511090d0f06020d151d0f0901140412111c0c081b010219020f030d110702030f1c05 67
    0x807035080013008881000b823a00d404000350000d01d015140f0f9500c0d000c0d011400c0000c03070b401100240c0000d003020041c001040294001d000660701d64424002c0c0329410250420f032910b40c811001550009410811051101488081914650000e01303840e000504440c4031926140310b01d000312200c60100f140c4000680c030318442c500c43c01009a0059042132254401e10442e0090044151410006411003200140b080e000420041c1440d540200303011200c400341c2d5103910b9035034120118850205403201e0b60b0b450b006409603400a41038040c6c0d0300a86a0741c0c1c803c2d00510650780440382c0c2034600300400c000c2c09150f2490328945600c5544200941c1201c04d0300c1502c648180c2c14030140d221041c3c016102c070394070070b00e02940c6c80b9016106980c9003040c0500c0c00440e141380711100003d0769402181c0040380210240710f0b178803410340c1070000d4041035400a0150343c80c0d01c01c4004030341c01151740c1c40640c02e00001a0080c2d6210b0b65000d41100e40c000b02994040d60340d22860034210020b001e08414041045100b802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 355411933 1250 355410683 355410709
    0x20109120602070212030a08184b030304021909060603020304021002010506010e0111030903010e011b09030c051e030f0124270e0304030b100e04050c0d02040b06040305010e0c 77
    0x5071718403c03074988800246c0c417203034801d6003a1168401c40c8541c00750100b644240f5044980c1142030b021441800ac0b8805040108100030704d00c0700f06a100782c01c2d915000201c2141c0d400340e81100c0104514100c920b0409401081c0d80108401c80c2c40d200c000715034150954020750145008640a03d4803102c404400c80c20f80b0b0044072080e00240310f9030032075105540202d180841040c0b80206072402e1201800119007140c1c3c1d203040e0248240e440d00038200701c60211002d00041e24400c3d02d007260205040d5140c141b4490010f2140b14020014180d840c0d001c01c806001d00415083e00905444c3700303541464140b8060244a808000d02c0140da050402c100c3c2c0c91071069030100e6000d0207441e00b040103c41160000c0001c9000d90460140d10f446085d88101e9042c070090000e107104484120307560510040c0c403000d000aa0b00040c0320b0304001014440401c00c00942c2c618030040449000031a020740d440854090003000c030455412050100300401080010f400c118400c6070028221440c440404c0200510b011840c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 355413183 1250 355411933 355411937
    0xa14090315040c1d04020a0e330414040506010e1618170d02010e0d090b090f040f0209120114071b0c06080106020105100e0112020109120602070212030a 67
    0x9200e154846058801a5070283c02001640c2c074442d0303201c00800340480c500b8040b00c20350007000c0c1040118074240c61810041c240c24213400c5402d20308000465040e40240045200c5104940001032481c484c036901d8200b01600940f090250a10112260255000c1500d044510f8010000081010a01b41603103911030000940180c0042d85c0091040c2c03048804241203c0030031078203240204048030680d0120748c18000160003001f000611400003401c4038040c1c44606201c3c5c010500c81a003845e0f01416600a54150380c0c030203036a0f03111101c00070342a80c076000c1c0d81541181c24a1014940c46040f80d005c0c2c40c8040c4283c0700214008140e0310384500f21445841c0c402807501408001c101058171550780c54141000182218080517803a0321a114008126406040060607020041c05070716420702a060b08180c890100960f45030600d002000c0000f014040e42c0d01c0d90081d10244003c0da0f00c5414100c0c010034505031600030304015800d025019610094050b40500544000d8205a18000003118002401c80d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 355414433 1250 355413183 355413193
    0x3180607120213030b070206061206010e06210f0c0f0d1707050304090f09020414040c031101120e010218090408120601050c010c0914060f030c07060e060403050a140903 74
    0x4812800081d0450251200025a030f150044001480c0b603038058000c03c0280c00034422403404508000306016928540c1007540c0005004004105e00068120741001c0c0c200c43e100041d031400c040c0a80c0d03100e80121700060a00c500d0800c4400c601340442c445444006c00c2d90100c0782201108140815156480030084c001c0001c100c0b40981c0e026042c0103001d07031a120314152450195200300e40004d5a114503c2040800c3d9503801c0d8a046151510544000403608903500c011854251914880f4010703512024040c141a0310a507102c0d40e20138520b008403814052010801e5944800c840b034000d411240301807455039030350545030306189044c04989204a0307000020520f408100300e00d000c030204010b02000d040c40003e00c40300e010484280039100d1030110796500c0d00450703072a04810803c8180003000c002d010390700401007102200442411a940108004800ca030360f584103142040091110783c81102040c01344906010425038814002d101401d46955150302807000d0180101881c400c0410b840c1d459406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 355415683 1250 355414433 355414457
    0x120103110109050a0923010b0a03200d20040503030d020901032306010905010e0a050405060604170303010f15050a1d060307020102040614090a050d150f0203180607 72
    0x866031480030008185042c54400e555100800c80b600002e4210402181d00d4031115449aa4040201240080e044c414041203502d4400c2d02d500c1ca11600908808040e142e41100242c16401d55010b68060003800c0f1599031604541c618100a10350302c449100d01c40104c070b82844100e03440006440c183c4900501851400c0780c8210554003d51121242d03d0603d40c50700c103080c40e00c81c00d45410001d1050030908400987c44c28000040024809401040c10300c0307080e0045140302e4941e45003c809503081130b46c0010741522108002603550080d03501c1001042c030b211a40d03002c0010003201860403101c1d8541030780312032038885c0300403030003401d00e006250b0000e0000d00c20305035190b2003031041141d009081070511140f110503002140300ba500441e00c550142c0c0d0006002c210655009035101021050860103174180b00b412000521417000382d102d8548a00701c100e800c0d0301807101070480500480c3c1030740e000300519028050003030042e420131900304000c0d0191640040845d0070200d40c40d071042c0981d0b543c05440e040303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 355416933 1250 355415683 355415693
    0x3090507051f050a0e0301090c1814010b0f0c03070f02010206091f020315040617070b03060d020d14060106180b03070212030c0708040f1a1e07060f0c09050901080102120103 76
    0x2000302d480303080040d000249400c0d86c0742881002e913960b000e4108992030504001c0e501c1d40c40083c6030382c150101860b10028400c2441c00c0000b940c19103200c180001e940726a0f110a07a003143c01800360042440c080007a583c0c04028140115240840c400e03001e940d06a030755213608030b4490305583c480c0003070043d080450720340045190b4001c42e4800000d03900368a0b074256001c04034088a0503600a4113044181d00d1a04074860001c01c1102c0042c07580d000440c1c03442c0b0b07102001c1260f0341920a4000c0c061001c018902c0100f00444c601c4007a101403150880d0700542c1d6681c8018100032801200841c96400c1c03060114242c040802103a2181d0b246400500d43d10034001c41c00a2903520080c200e800c15501400300d01e0000d214070008100900c1c1080510302620300707060510014014013007549500640400c00c904905100580407111401d900791801c2d15401c860030081d01070300d141ca500827100c500c1c0c501c2960395940c00540035000e58a0544800c21185e2300d0352101800c0344035100c61a0281c803c0304004000040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 355418183 1250 355416933 355416937
    0x31014070c050309450a091a040204140c090a05060a0e190503070e01150c2a050607120e040b0f0f060c06091b0604060c021207080d03090507051f05 65
    0xb90b109500300380c2c4005a260712941c00e1540b1060101140c048600008040c04a400e1b410905112081018000a0b03483c03103c8450b5044c00803a0f61030000000506541d42d43d840341544180d038694045603840e10440c00d000d030f940121145031040207034040c00714039802e00005681001c80e00d91a03045016450000b0000d000c81c2e81c2c2d1046085621a2002142549050045400038082000f9000440d41400c20500c2d8100600440300108506801410040340341104080c141900303104541e0030b0f80030002d001106040194015075000800051280c0c20812009080c026494440c0c0d81c00c04101942420842941d522103509607015404135030840b49031400d040281041403001300301c0d030300e00b40d80380c0031aa06221b412a5900065044400c03480c04490211204090a40c000c4607914901810000b014014000d1070101031b004a855030301c411040c000410100c0d000c0d04941c0111403107040c4d114001000382444c1e120803a52401040300018140c14000501000d00c803281401d01d0300034440c2c010032034541e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 355419433 1250 355418183 355418209
    0x305070206070f061517030a08070f0c05010c0c0203010c0804081827040b070513060302030901180825080904050402190308090411090916050702031014070c050309 72
    0x914a4803403614001043c41c0b0800c580c01c014504d40d502d48031b11300b401603068504030168240d22600304104030410240c0c0b2041c501e80c091418203004070b60410f109401c031050401d507440109158a8451000c1056820029004640b0f100b10003d000c0d80301c00402c100d541410030748004041c0c44007488441d03801e10340c0751070f0407410b040d018100d400c089020300d2101070300705c40c14145100714541080a000c180071040300c010340e01c0500d07810300601d070049441755000754200074800d0500301030f408404140601020f40012080b82400e6469903030f01100c17418104415400101e00251710840003100b2000007108002000310030380c00a286d2800c02e4804000c2c031010348801001281c0c083c8051501040c07110308082440702950080c0440c81c0c6401011040c002110514400c0111090041c0005042591034030880c1e544041c1c0e0100394801e12126207000e9819008aa030020340c1801105480030841905500c030f560144800417000f40240c48a92041d91241d52034140945290404c000102c20b508000705c0c81440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 355420683 1250 355419433 355419443
    0x504090606050c0a0b070212070b010503010b1507020f0609031e0601060e18070c05030310090b090405340902090406090e03070f080415020c0301050609060310050a0e060c0d051003030507020607 85
    0x256808c2c107140c01240c0d400341c5400c0f40c18842c0d100c01800780d03080900c00c034160207070140c480000e203400c0e2214040b03d40c090443c000344142c0310200015060380700c0a00381c5401020140413202e0a80150810207441c40080040485a22402c0000691503100300080341c1c0c40d00c001342103800c02c16504209803003a540008e00f50420300c02c515007074000042080008600c43c900c1c0544201a03a403d22520b0070917070b9221408036106075082010f02012070400302d25060504101c50319200740341e9030200b604004107080b40080221000007400054454500d400038203418108980c02c003d4262030f01c0f001022120106010300d00c55206100303c00010320440381c810032080c01884100d0400380c2e6164038440d082d90fa01900c0005801120325401303503007002d0054a0b0440f00440f1294401e02d08600400d0b41d43d1f80804030302c11000d456401050f1400b08651101b40c1c00c1802038181d40070b80c0f825800403a000c0c1d1290616540325454140081c06039403880c1e45030000e899141da2854641003041d02001225000700c0303400e4070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 355421933 1250 355420683 355420693
    0x619060f032a05031b0304111e03031b15011a0a0c020a0f031e0203120a03020904060602070e1506030a09020111010f0b0a080606090412090e070504090606050c0a0b0702 74
    0x1181d5203403214800c1140403d0361107958a01e40b035038000a01010340401030001010600902c800144d400c440000000c0d016203000904000c8040e0711151820110401074150000050500c0c00384030340706102d05000092800c44141014040510400e0380003445083c802c0031189090480707016100d0010014940c1030310b49681c1451440d000266014015070180342c81c80d01c425010810486508c8000f40b5400d0341c1081584401e8017900800e8a5500940c02d2499500001a0814070103002c0d0341507440b4114090810440300c0c1d1101d4001c0d55070103030307402600b0400c0d4003040050f41e06082e540030619800c5010740400c0c25910340484001c05400e0b0740108a0500625400024285609100341c018280340b141e004135013000309000380422688140c0084c2c506d50442d9081000c551115103105821580c03010aa00c0d04090086040310707246010780203c00400e160f442030185943c0d2200140040e5607100c50700304640c554500c010344503880303071104420b542d81104000c8008105d2034600345600901c1030050b96 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 355423183 1250 355421933 355421981
    0x1a03031c091a01090c080105181504060315050615030907051507050118020f011704170f0c0c040b0406081e0118141b060301150504030b070201050619060f03 69
    0x700e06082604550030031544c45d078010300724540c4450440c2c0142130548030400f41c0406011149541100101071500055907024004003031784580e4844801160404012564460343c007040034050311007030f81c031688a420321046010550b05102c2c1100d008414400c01000c6840c6060b082c040c1490582c8180c1850000522105020500a002c3c0100d00395144c008207080300070ba0700c1000381155071606200e04000400110303000ba480f440d0802034006400c0000000d10006100c0e107800300380704081e624480c544010410300ca0b418000202e030a00760004542c28400500590706200444a051107000159480216060392103800402c142c01c51a610740004990030f08003958180400b858808119500031919151000d0390405200b100c104031450f001c0c03801c007407410400107000741c00306005da101c11001c04500c07040c019000b50102c0700159448004901c16180c0400d002e4020a000c440c41030261801805440c07800d8503001c443e4090f1560750712450801b905901085005041c40d000d904640010708440c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 355424433 1250 355423183 355423223
    0x10030e030d090615091b030501180519140109050f1b09120f030901120507081824010305063304180f15050601050a0804030e12011a03031c09 62
    0x1d0300034140c038080c0800d0f004082d8681b1412000e9071003211082502c1c280c0140152050204d6000c00c0094120f400b041d00d44420100700c0340d503007010090795411840c01a107104100e50b5102d4007030494407511410001651040e14100240a0481d0100103141c0466076101c0f25008070006812018005000342c1d5100980701d03c0c0e14a020a07c0000040a9001042c48103207584d02c24200908102100014880e600340348001900c41c3d03001604081e2612403c4d03400d000880e10400c0001c41c9111425800201c0c80d0000901c0000303d402030109031403d0207045d00081c030900c0c18400e640608103c0d5082141c240d00100040d0003600c2610800e41ea01ca600c03119500d8550051801b5192424018030564400c14018500241c040d1608505492494100401c020142c1e0b00b180c02e940c6103135054100000140e881e85011244034107102c00c0c15601c00c412604a260140056200055424072881c130340040c42110801c1694900038003d80c0016625507406500011000da00100c011900c81c410f802c2100c2021800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 355425683 1250 355424433 355424471
    0x41e0209091b1207030803060303221a0304030c080903010b060309060a060602070b270607051b0102010213050607050a020306180c0603090a1202030c070305030910030e030d0906 78
    0x401d0694444502c64501d42e202840b0109141c0d03044500000696003083c640d0b4641e6054800908500b401200052241d2001d20071206120840d0b151200b00402810140c140d150460017070105400d210004042281c9140d002ca074003940d055140c0701620341607070b5070711405a0b00c901070b429055525546511065254000503501030b000d0400640b2107031800b4920101211140e51144007158030451003040000c0100c01180c10030040f0001d43c2100c540d4581c01903270254103035034010750030250000b080000d102c00030400306001c9049040d10b9410102c600c004a0903800f6980c20044083d505100800c05440c115008280c81031262090b1140307110682c00081c24000c040b541480b07807203142c00703019412007001d009006401404036000c50540c1002c00c2441e942e2082c00c2802071054101400500241340200140d4442c086240100c58200751203150054070f942204003500d004000c3c50221442c1a07000c0e0080751b50744101e0314019810882e048100c24080e000002041c1c800640d00c0d007a103811130403010350b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 355426933 1250 355425683 355425691
    0x18010c02030717030105100806030a170c120301060504060c260d0e03030f060108090a12030207030201110412023606031009260f0703090f080a0b041e0209 68
    0x9580c562810b800c2001040d940035018020410003080148111f80c0c5844c0da0081142d040d241c568071036902d44011a25001c640d220140c8410b502d4a00325070185c00502c014002d400d1640141c0f075400c9002030315554580828004c000200342e0501c42404444d2180c6680c24405000d03008660744046005187c2c0f01d082510022160300d10b200203980b5505880500400890350040001541b440ca4000034406090102a000c42e041281030008101e02060800c0f03030710402a0000c09108013242ea100024000794006030086000d03500b001e00c1d001544c0c60620a0724201c0d0441c01c0703404403080b031aa0800844040c1c0051007600c411051480142c0b0424548100030f890250300040452170804c0c804151800c24880f000300315160400c0c1d40703400001e4a9032a01e8803030780c41c5c01180c150101c01010880e90280a080c12102d02d080011070018149a8001d0740d03041214283c030b0040c0720303030394031400b8843d202c090005024080e20405c030040760001d04a060300c0080c0488080144840c0480da0380003c203020f10581d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 355428183 1250 355426933 355426937
    0xd020f22060e03030a11030c010e160906030c060c0510050403050912011e0f06051905010801080d05033114011d070b07080c07090903090501031e0518010c 68
    0x6603403240e9608050300c900094201c0d82032a0b44480c0526001a6880c45420700400800c210120030300c0b0303c40307420003d494010040740d000b0b001030030000319126919643c00242d112001e0031701c140060b420185200310800da90f00441010422420154255400050080101d42510030b07441140000085440713840c0c0690f20960350740c1d5a0751821020000d07444610569840c40e6490300381240b00783d20801c02c042d880c01c8618003001c501001000d08210003400203912464000c0c5911180869000c1e40c0c698038000d0b104d0988501046903203804401c0c6e03407007143d0758046021581c1000840e03600d86403a080805100d0600e02280200103d003d1204100c1d220381e08110f82c1d40b50300c08034284103a5400e00039980c20007007000b5240c00840e01c02030419920222489040c031000e000184910074080324104442402040304226540700d0703900c080c40d2004111030f04042c1c00003032140703030702080940c8a80500450390740201001c003821030550702c081000b440c010741086200005641d10505002c000c0c003808aa494150b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 355429433 1250 355428183 355428217
    0x9020f1312020108070f0c020f040b060406030905070605070203030d020705010603140105070908030f0a050904060302060c10050c0703080f0619080d030b0d0b390c100902010806060d020f 82
    0x5200141c0200c5010b0080000d0042c0304612441b5a580600804c542d1601102d0498030a800203020600504012216071b80100c0f0028011a516425400098034103106204032504581e40301400c445900401c07070b001358150802c11503446014000d8021707000c603e014000028606591395a5400161803114a404444e5110800c00541540003910100248007010281d07152946d100f51131280d41c070035071682a00f888408510800c15440c1d60740320002943c0c1c0a0b1540daa2840c0f1444a0b659400280d6050342106040000041c12001a0415200804d5050301c0304800303500d50f584885060340c0c0080c112a0410010709c020381440051030000e070001d01503a8050084120341c81401000d448020301d030980191854140070f400039440740388150b40111490403405910315028400d02c19806421032030340017900649001107a20702d810000386201c03402c01d02101d0359440c0c0d0300b002c8000d48001c03020103804100c06000040b01d50404100a010784480c65a0041c0f0300300d4078000801b20341ccc00000325440c106803a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 355430683 1250 355429433 355429469
    0x6060e0a09050c030703032f0709090209010609030312052805100819080a180b030105040501090e1209010c060f090b13120e06070605070e1c02010909020f13 69
    0xe0100032400303442a8007070b1050505540b40a44412840a4003c101e001404803451a402090000d2448e0140d0324096410127551006040060402c031070b4203034840d22812000168480c010b50410003101e9040c0c0300d064031040803000010040c40010040085000d10740781003072807041c05c0991098030052880c00003230f00d8281401880804071454010580c103610840a22446042154040360b2844d80825025a182000b5600700da03001c0340e14036050780790a902e000125012940e079014606071041560100102da83c4c03204030909652000306643d416402080464001e020020010140400b040c10004c2c902c0f840c41c3e079000c04540c1250741440000381d440051a0800143c01c03206034001c1c5020102c078440003130035102c4500f0fa00254201c0b00c18040f0036804203260382c0300c00d0203030703074000c0d0b0840030800c81490200390103001c21301d00b040c415205050070084521140c50280907818125010381d142034003941854800e00096001010b0b2015281b42400b1089542407041c84002c0a0300f0252a03040d01152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 355431933 1250 355430683 355430693
    0x20a11030a12200708180a03050106150311090f012003040314010b13090c0306090b07180b04060804080d0e0a03030e0102190c06060807170c0603070206070c06060e0a09 74
    0x401224160b480b81c080700480d600791826403d944013160040440c90740d4030311030202025a4030ba03c1143c50340203070031988000103109040d40840d044500c219084601c601c07000000f01c04a8008080140302c00f2002d1003040d000b81002a10406500010b052020320103e07a142d0820001d0300d4101d04800c00e90000400340100070880a04200c8220031800a02502402038005411194802500e0811a030b4840a00b0103000211820400a540281c07003004141e01038108600d00040c110303010008510000750400305060710a4500c41194010b2500f241044c0c104542160100000381040e03900394010f02c54070194400320310401680030902001000300649910b00901518100d2440340201d91042c028900400352201c0c201180108500d03043e14016041c0c07a01d88000c0c60300f43c0040c501d9120f44c29012420384100c160380002c0b09255400c4a00c0c80e41400c0400289200032100392005070000c41c04544843d004000076407010384903520208103945c6074014420825002c0740d089a82c40c0d1070b0130030442441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 355433183 1250 355431933 355431941
    0xb1b0d060f231201060b0708040303020f06060a09020a02010618020c0706110309040b01050d05100f470c10060801020a080f0717040b0105100503070909020a11030a12 73
    0x60500e1485401c0700041c1c8041c2c076407282d159585805a0031900601496203020351005010b4a14200383c50780701c0f401ca0405107501d8029020480142c461581c50b410203100009400b441003000a05404000d410a2050b8010350016440d5006541d04d8040200f030b1b44404050840242e03405160040e218046c0f8001a4542000340d070050050110221002040740c00100844406200c1560041103110140004a66500c141c2c0141c0791034900d00001d20a10485003040c41c1c007118031303504010a00d0f0761680802d0402d01c8102580c0038082d0401c1c04e16008400e40030b020300b080000485003440d0125424201403c00c4d51180120344541d0304201c15903040300f01756105030300160207085c1c02142059001c80c0c010304000c6c0c010740082c0038000034000294141703204050311a03581000c00b48083c114102840c00203401d910a00603503104602581207040d41e1031003803065900c42c4c141d50380e9014200f80b0300b402d1000290322400c2c0c04401c1003030059074510720520410040c07580800300d030354418620000342f061034121 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 355434433 1250 355433183 355433189
    0x3010e0f21070302070509100e0406061a09060d09020f1002061f0302030a02010c060f0207080306180f0c0d060f0803090427020103020315040c08070e09040305070b1b0d060f 76
    0x740820b00c02440865800520071007a80c90644540c02c6544442c200e03505201c566600c0700b08504007942c01c0004204403a0401070032604192001074851500008420960007051126034010780306000e1205100d0050b0042c14a0700d0010f0610318505000202162015512013240d1000d07134052400d105001642403003c0e035440c05495030b1040e2141c00d503800a6101d400703a40010b8104541202d87d00300340322031a84542ea20000b1903038215514003092502c2a8540c00848800b07100d914460700058119014103461403080b07251107030304495580c40d00c0e550005900a03201100300341c1d0381c07444041020080302c20340303d025180303100045031070700400400c2100b620a01c4101e801d4281141d10818841410081c0d081200c6509081c05601d9543c2c4820f28400450800216644117041400800321b10b9080f41580d03024003280e6488030088000340c0140400350005441c02070004030304000c144003140d180c1c41401d0304441e245991460041c6801c100c266503400003042c0080c19541c0e401e007045240d18084100e002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 355435683 1250 355434433 355434493
    0x30703022a060f130b0a17011406030c1b06040c050f0d0b07051605070e100e060a140103180c05120606240d060303050d0501050105030609041103010e0f 67
    0x1c0c0384415010840d81d000c0d124a10260507804114400d81e01d00c030510f207101130300c207991605850310003600b002820031000c0441761004d28081000800c1c1096084401c01445401405075031070354807481500000742c0d00400d4814441e00d41c407d00184c2d003c0050001e40e0041e40280310005101307050008108141300c0c0304440a00c0b034990062039a0028508824a81d40500c240c10000d45804064a2503a0000703805480140540107100d40442c024107000c500d02d02401000d207940c044c194454000044a080c207480701a0b10800780d503010000c000c4076012103a00e0381c1e818034022402c20005050072012490512040b41c03003c0520805025608108040401840d0800c00a08003800c010380030403102d401100690720201c0103e07851200000c524001c840a540c04010100100b80d03890500501540014100840060034400001200d40c40340b01a6801100001d044d120162070b103580d55003441061481d1700b44c055480f50003d40015109206405480d212200984171032904524081500013619408401c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 355436933 1250 355435683 355435753
    0xc02030c0703110a170303160903030c080a050712020a14011a0f0a1503020c100605090604050402032a21030712090e0406020a0809010b010e0d1403070302 68
    0x6000400164542140c1d008110a0400941040130a1a0041507081401c0c0344803485104055800000000c51148110305a4080c071405070a00403a9120018840a0000b0b02811820000704000400030039008050b030500341d25002c1103a0342c80d1003549071a240e120168114015800900203c29640301c108a501002045500140d102e40f402410b515912035001e500002502142074461181034800742c844140041030604203010001d000c0e600c00d900a0f216409058104000c00e0260f00501d000d4480c01000808582e4034001804003e100003082aa810301c19051902214031414a4512580c1c401c840f24210050000701804002d503075061251100040f4001480c10400d404816940150b500400240303510300d200d00100c0703820781540c001091210b005010f02c0200161603004054480c481d440b40d035507079580e0700002c0d800c80303d035843c403c4e02041c15480d24a40741d01d0807201804000c0d10a504060078421003401c03191954101513402c9016034040b00c0c1070803540c03d00c411900035100c419146e0003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 355438183 1250 355436933 355436947
    0x209010e0c07080f120f100911030a050601020a1b0e16020d050304030e040c0806040c0809100209010201091b05130b011e0c171815070201080c120903030105040c0203 73
    0x600500c682d91018104040105600d0300065a031001c0f5070f602c40d01c19000150038209060182800368050b01d001242c0c642d9804009100c0440d40624048500c00c02829410b60f41e46e03070185806000c000706401e0440c0182201c00700001c10301d451000314004960448104c10741003070b0300c4d0381c103c140103450035403014609010b00721441e9002501601c42e05440ca0010344a4407280b07000e403a5011140003d076409410000d1000302d07150b0044469200340c4046505101c1c40c4c0d440c690503200c42e441500c0b03220380e030740203c140345c08800dc4c0c50f0000c01160f035040c0b0000651000700d031a0081d000b17500c030a90b9030324012081c03010001c602d004524002d203900081c0c02007180c4413003140081d1141c6540c130200c1500491200510400700e0040d2450140e4076042040c0c01c00040c02e0304024070940d40700b01e105205400600d541082c060030a02d00d00c1000504100e0810301e847c2c402c0e0015201008010011030840d03804015a20741c4140c4102030a0080601e04015074803541424108000d42d60014007a07003c551080c8641 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 355439433 1250 355438183 355438201
    0x1b11030a061e020c03031b130905070e060712110a050f030702030c0a0b0702040b040605180402090106020a0803041704051c030206070f0e090601110316290c0c0307021203070209010e 80
    0x5980000382e42049000000c848240b07c0402d000710310088107111500d280c0003904078550307005103110320101d5440c03d0035206e068041103070b280244040640811400181c0b05801401000407449100348242103821404880d030301d4900c2c107200441900c4841c1c0010410004509007002211482841250785458290500035522854029810040e200f00c0d00ca8006011035241d44d13100030084d010140c0452104c50303107108400c100305000e0702c0c01c80c00703885110000200300f03101044100e0510f0744800c000d8a15155900e0307000d030b40a42014000c4042604100004030356940481e0001c0c08100c0350886403d4400c203007070182c1031480051055040c40614031030710f00c0c079907801500b010301c1c41401c40f82402540c0b13960780101c52400481e08154820701c00001c41c0001d012241c0008039071148162400c80c0c508800404450b220b9481589401c20965002c021601580c045000752000c042520216401c000c8150001004d42004130100c0040f9080052818151f04041d2040c0740500300d074040310100d9040211038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 355440683 1250 355439433 355439437
    0x504020406020607052503170c03090327040c1206060f120c03060e130c0f21110603010906030b060d082d03040c0f060309031b11030a061e020c03 64
    0x5813004000000600b41d20300e42c0040803906091000070140d04014043e407a000d070403400c040011006800c2c070100040c0c0148480001c0364852021748014500b043c00500d03408510340100801c00059603000d040c1c03241c241c0c031240309000102000340e6951400228140e00c0c542100ca058201c0c40410802880e00c0d01469041607090f500f104000c0b40004038415409030890080048da0000000c2010743c1c805d11200001c241035207540d4a02500e05254450f17500c2480007245800c3d4814103200700e902900e040305286050b04200c0740240035074070a030210081e402c005020f5600c0dd810218a85d69151418400c0c08002c2900070f90104c0240c0e038541502c0d007036840d107082c01c0c000c0306100342c0029002c070481000c1e9501c00202c203002c84101c400d49900c90500e494035004d654141d0081c030255840b012030020340703540300b07009480b00140c0680f550340307100c440340314a00c0d481422040300b56038040400c800342000f51410040d00b0451400742d2400280c00e442c0307050321210b6014500160709400d005100241c0080d5000c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 355441933 1250 355440683 355440691
    0x20c0c090a05063d020106090605011e05090a0b0418050601180b0f0d02070c2103170612030a0801080c180a0b01030e0d0201060305010f14041202100905070302030705040204060206 79
    0x42080110411202030320700f000d5485000858a048042d074130310519405421100549051420078000140c4a0004480f407421421600c40111210311400310282c0c05a001000049009080310741810b0300c4402c403aa403980a40d0155040c107160100c41c6805412a00c100c0d504041d00b441c1080440807454a400700246060042e03e91342103000402c1400e0f00440e100711107071300502110a544032060f03030520303211841e003e10540c460b01301c013024a001c0351201070b80803c5a45074541c80c0c2441c0040c0c000110288400300500c21a007007184641c4c50b8041c000c00700080d00401400341d0707036041198104422242065207001c2c0890003500e02c04c1010314021007690300c699010101c00000228682c01d880124041d2000500c00c0d0100d0040c4600c500d04680d064000a05032400740b4005d20140034004004001c036040a0b500010802290300441c2c00140e554a030326413180c0b041c0c4116803113a4131b00f594460858152a10403a1035911030703501001181402e00100c0010081103070210300b0986407010181d255078000b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 355443183 1250 355441933 355441969
    0xb180702070f1d0709050618010e06040b0c07060e060909310605010b0333130204050111010b03030403021203130611010b1207050103150801020c0c090a0506 69
    0x24102610810054008018440c1e6410380d060350b078007a0301402c40c9404080300389040350100203020540501c0c46601102c002400d10740c941a01e450040b01c143c4240000d4904000d41220301c0d071125038446000d00301911400400d103586501d03c01c403040c0b40c460503500c40b006102010040c4035050342c1d10003d98004560581f0344403a155a00340c0d0000c02d030001542035180c4a0040074440201c1c102a0040c042c0c414810751041085036220110b40001c5d000413603880c203010a594000080344004075043c401c003003151340038520a288031407000038010320301c05c0f01c0041000c1c1d010a0420280d81d0010500081035040402000b01c201c2c1e21000c00d0300c071302c124013010b406680c614941301007205080045985200031951040c030f100340c0b05c500c01090001c840d513003450b9540c285034800386d01d8541514905151110135004080b840e14010044d4090300440321030503200c1d03801d4100000d4040080c0010000da4440d2405440b85607d40c000308a4281c102500c04507815103060100032183e29000401400c240c118 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 355444433 1250 355443183 355443229
    0x435121c05060a21021e10080112020d03111e16030206070602160803090705090114100f03060b07050604020109120b060103050c1908160c031407031403090706080a0b 73
    0x110420004039001250001d4200302110503610020b0100044c0c1c418036030041f0781c2c1d90b21400c008001207440314403e010300039608480110308001031a2040002c00850301c20f04103032901c204144051803d08042c0000003000c20303030b6003840c1403400005111011441880c50212010726082d500402c0a502440800030001c1e03600162a025101b003404400c04259440b804555591404400060316500d8034400c0070300030400c000021800c242117454549040e600901803070301c00ca00102040f2183c4480b61028418542e1300c82e00411a840c8002c01440300a0040004054a04142c0300060041d055903011403400442c0f41048800540800c403500c4d08403100b46400b059580702d120100241e403054000e801c04440d41c0300a1148125003108219200d50324036422425802040c81c0e042d40d41020140c8000c0005200301420300d860843d0300c015000740ca002c2e2500d684406d115403050702e51a40f0507195203426502101c0104002640300d0030503980051404000d01c003003922180407035040b0426801c01000e400c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 355445683 1250 355444433 355444469
    0x1120203121605060109090f021306050a08150a110a2303010e0403030b010212090904050c0306070801092004030b0711030307090501080c0435121c05060a 68
    0x30421800c0010034107030410715514150100b02a400c1040072004071414003401000003a0718034548035030b1450b9500054070b03e008218603401c000c0040d868440e4038800300d0b520703c8045080c2c1c65948406001e003600364003c1004030304055407001e0440c0002c10603541d66060840450342c2042d554160341d451513003410176115056400404120b80a41c401d20784002c0a40800001003045d880b40c00140150f0107528100600b81500d07004903200d0911072103d03503c02400300000300e96424240805a4414020700a542c00441040006800d1a105035420000075810000502c8510070f180b142d90100c202d004c1011207800c0310395030001010b0189102c0074142142c6603002840c1c040c05103210922503655001a41d50780d14080301c02a00d40821030180600188611001030154100c400889042c1d40240003004450010b00c9001011200d16410340c21024024031080314204104101e8544102207022403140c40b0703584034041000c0310031001d1031141c0c2c150414050020301d4840100c05c0c1d080e0780a0302c114080201e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 355446933 1250 355445683 355445689
    0xc040605010c0212031905120a0b1c0501060e130b010f0807181b0210060504020c0c060c0f0304030302060402010e1e01110a020303040f03030e090c090d0c1d0403030e010204080303011202 82
    0x14411488946d48031200308005501c3d44071000740012080c1004c0a42c117601c42005504c200d40500300350680003402e042111006180008058240c0d621401c0041051ba40701c0c000400300c84001c0e04c0c40241c1e8070600000c003007000180c60b00c0c503000d41220016408110718110360743d0b9955030f0f24400d00c00b0000c2e85180c1d00c04040407982288582102d50200700c0210100320070029903600558a8800c105460302c80080389514040c0201d808940d41c0400030300402071141c0c1004017590200c000c0304494400d4200d11075000744244098001103000390040e0141d450640005442d02c3d441001181c401c080580c103c549900200e1022003042c0e0084c40c0812800c404010b18501c3c09102000c083d50601c0003003400101c0012841c400002e0300c1c0319a5484440441d984180040035000351103140c80e401007800712603060f01380140c00142d614020300440b007e04d44c3d20b41050190700022410052032660300010042855003502802d15020240c0e030003107141c0303890005101d44a010600410321059620380300e541c00d43da = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 355448183 1250 355446933 355446937
    0x6020313050a0b0906091603060b1c0b060a0e191104051306180e0604030302030a06030f030f0206181209041409060411100e120a060614030c040605010c021203 70
    0x340e4080212003198030380d4200010001d90440b1400164420040010450705022488440e4002d401032040e005500b140d403418007900d803100116800103580d01c2c45042c18814880d0600c1c5030350203075400121a0400c2020700040345010b40010786004e00c10800d00c050b422140c1c18504014082c144c001540452300c1c01811264810790703000f0b07a440038411700460794000c12580301d80c08454001720280d00c0c4500140038481596901d000d4501550840000070700440d000c3e400456107d80c1c0201c00151244d104d6984c44d1680c11680c1c01540000c40c0041e0200e603041c2c0410030140c2008802c007803601d0500070201e445649001289101241c80c002140070302407503e40350407440320b4500402449080b4079201403072030b903140381c1102c0c1520075014201520285081c9001e4958100490351350741c043d244030307031010b100720825400482a01c80c81030700d00100118540d480341101a00e0007089569110540000700b600e0600018441071081f46840010800ca0780c200c901c16030f501d170741a0b84842c070351648040864214 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 355449433 1250 355448183 355448221
    0x4050f030c04050702071409010b0301030318030210050307230301051e0a140109062303090a020d0629090a09020303190e0108010801050709031104020f0f0c012304060203 75
    0x102e82080b040c000495004954401a14800c1c00001ca81e440c00008110300110284a4a81030000c20001800440e10440c5011220803006e0030320300c0000d0fa694080b525420380d42c841900090000f0040c0311466900c140641900350100007038803a104a4030102400c1d9100620139648580d014803080b01300c2851016a82404060091001208039652011800d1901d1242d20700c500050b5103000101790603000742e2141006080c108204c801c0c511107034103c106154005046c07a00148540381128005980e4007403078000480c8502d4010502d035400030350001e5526000026a130100c0e04503074543e101500c40b0509103900a9114002060306866030000c282103204686000307108016141c074030b07800250002034034030140c503003a6510300143e81d840000300d00700c600646200e00029081d40040010400801a034111044020320040c034001c01c101984649901c5071041f14107903a004074072540600c000703107e0905209291026440c88500320304103128041c070000c100801c59680400401e030911403c600941078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 355450683 1250 355449433 355449439
    0x100e06100e09060d020a0308071a09060f0c070f0615080a1a0a0e07081b0f091303030e030a1d030109020306130503120903030402031c0f05030a02090603190608010c0504050f030c 78
    0xc1e29489040523015a400500d0136111621081403131442146031403180b9102d0b20090b07014080035100d02c0c40d01004008080e021025000d000e11030080400c02c1180d14424071845480700041000041000078044002075015641c150000c8204001064200d0071404494040b4101c50032140e9170381d0400c200500c04688200717807600c101103000ca4050700018440010210a03030321100c01c036010100300004620b120f80c07040d03040100c078401b04014a0094070b948545c01d01c02d04011034030782162010245183c200030856000941c88844050300d01d11220000e00307001d80154001d002c100c1d00c0790003003075640310040c114400600c1000069428000c01f88140c4240c880550a9007174241003d15010381c0e06d402c2590180d210f4098600d04242280c14014202c0b54849143c40b028100186e0b00d40940307136a0001400413020341e4003000751140941c2c5842c000e611804512605044d50024940070404698441e0030a6203140e00d050002c12803a0b800c0390946088400440c0c116100300c103100003103820304010000690f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 355451933 1250 355450683 355450699
    0x61015030b2704171c0b040e030c07030c050d0305040e132004050f0403020705010f0c050f071a0a02070b160b04060b1002150726100e06100e09060d02 66
    0x10409110b2030355000300e02407030000a6141e04e140c01801c0f40e00c240521240c0b004440e02240801e040582c101070340114008100203482c80103407005505540c445007243c003003030300308503c2403040105040048014103010788071141c002d07002c3d039805007080c40b4501505000300c0c88040040d1907031924015000f21f40c2d5100d103415804c2d0202103000007101000302c1d0024412402c150025111800c1071400038415500740c0d00074440c1d186400010346200c2c1c092441c010804c21101134600203c0e80c02c1002d01e010186020041c22414542942052240845110384085400400805024590004200c0d0031b031000340702100e503180d02e19035000c84a80303d81c081c000d0644400ca410042801499031010b003c484041e03a1040c4040c1c02c0c0001207072100e011102805609440314040743c00103124802600e614045005160f000d03981c3c003180905218400c5440c0c1c0c2c0c1c0807110b01000c1c4440070f0f298050030b810400980f59451400d001a90240c0315055400406000301500c000141e042d66881e00d20300042500900451 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 355453183 1250 355451933 355451989
    0xd0b060d0e15090d0819090b16030b0603090a020f0a0305060906090d05070c0b09031501240e0117100f180507020606090a090c210203061015030b 64
    0x340d150102c101000b44480030100015040c41808626603030040015030b00c0d18003540e94114180c1c070001e4080d5600300110342d9079600c440050302c90403419004190403403421080017900c0c440101a0352040000ea4090107090003030003410400014054441c0340c0c1156400e0800e100b000c00700e00000744980c405805880f0b200180308140c1c40120310180280b203164143d45801d4000fa20a8a682c071840d0070060101294000c00c101441002001d03199403480141078628082e81c54040d61070382a020b0b00070300d210b003034590740342003262030320190030444c0c00400c2c01d040082c1c150728800603203105414142d81c1078000ca0f000020b80d070700600d05120406010030842d8034080e6030700c2d488440c00800c0504d02c0102d21a1400c0003090f4810b00001d201071040758020b210042c1c80da500c445820142c41040403c40720003c01c61804201000101342203c240203400f010041809240d0040601d0281c0181404d0403c034075001301800b83c002518090030101c9002c3c00d004c01c1100709003001c59142030452100ea06c4d04840c0b40c0c161 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 355454433 1250 355453183 355453211
    0x4090206121f0e0619080d0c0503160302070e0a05060f1003060317130e0906070f03092f010306062c0d03020f100e0705040e03160c0503010f020f0d0b060d 68
    0x1950052106495900c264540c07481c501c0c51703039041c5000d080078680c0981c824440c2d00340703c3c000818003035103c3c1c030943e424220001c0050002a00428046015806c40b6006006001c2400b81c407550084003507c06100758200600443c20021080d05424021814429038000c114000c0d0802801150300910b8a06100c0e840c2d980b2007095000414090b00030440f001001038450303200b10449000c1d000b0b2101401c40d541760414142c07550561109501c051503200da21074804a0803841101036980700b811001d40600d20a801150600d520109559040c18501901803050640c03240c0102801c0801d01c2d45403024113580c5800052a1581c660400c0e0b100d0703265243c3c1d6040690120360031865424080031102120f82d1840b0860a803a5510748007072a507400140b00300020710341504013030120081523040e41d2805580b0a03019a140750411000c1c2c910010703c68040007142070910032003641c01c003210342c110306181c160001461184215203003d14055200d42d0803003229940c0c1011251035030342040d01045807144041c08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 355455683 1250 355454433 355454459
    0xc0601091b020303060a1e09060b130b03040c09020309010f0207080d0b030703080d0507050415200a080315061603020706020c060306060304061e020f04031104090206121f 75
    0x3200311407140d8405034020a0300002c00e803070042d00c009003c0c03e00e0b01e0a2038094685c858440d100041074400f4114001500300f014070403030001d0425440c03015542c030080740e2a4110040a0b601c07400310b0980810410001c1880304143d64252449003034007580da625803115060261103030003200000644009512420406440b0060182c003403030880034414034500710304250301d500030dd20010300004410400c81d540b542160740099030002c0d030303414500d08258035031000074505020300400d1070115005401c071070f03109541000145c22030300a8a000300f11036441992030f880b00340130182240860007083c038500401c5545000c11742d401001018803414002e003540c10000d558500b10711800c000350007443e03407503246d41c00c0c40400c41344240405050203140d503c0300c2c1e803000014104405440040c000c050411103c511413400200f045003803050900791258214140480b101b0701c49800030344298640304c400350068645205032184078050800343c1d0104d6962000c135051449442241c5a05010b0084000c9003074694544 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 355456933 1250 355455683 355455701
    0x90106090626030c030a05071e15060e070c0204020c3901020732220e03090a0303080a020f04150e03060c16050c0d03020105071409060304020103020901050c060109 72
    0x425200380c052101254491213240086400794000f000100e9201d8010002491500c1c810b04039003140d080481c8400204049410341103c14240301f80c0e4980c41044d103409140c3c0600507000c0004098104500b0140c0349410850009004a80200c1e40a150f5642031010100c12805c407801094852020550300884810f0200c1c1d0700c44802d21a454028954030004840055602c5840820312903420310380840e80703070011142954103010030b4a41e10b038006d0b1610021000072540040d042c1c030050880400c81000c1c4d490b107424030340d62680107101c60070300d0ba5a90b010640c100d98060815050303603290300402c00003911803140c07200e82d4402c002400003886c103280111100000c0c0503603150b031503d601803401c01d83c4464055070b21121407001400300a40344121240c0540e00f1501c02e400301c518920180e004600c3d5200c4082c1d044c0d001d80d56680030048042e030000403214108032004002454000c5200000303c140c000504081d042690215000f01907034003e04c210307107010300f041084510035a0769201590207094071036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 355458183 1250 355456933 355456979
    0x141504030c1e0909020a030201030e01092a06020609060402010f020312010315060e100e100801090515070203030108030f16060e1c0e0f0906010e210c06030708060103050901060906 79
    0x8000580d0fa44511401090990040c0142d07046455a00118040c08032a210904c0e2550f0710001a0000384064265000d0104100542c07804196410141410414164810340954202da810000c8660020551941c41f0703509007492040c060140c03508034558020074452a00c05010200080280218050298102c2010308000d01042d600c80810351f01040054500f84002c1600c620b0500c147c420010800764480309081443d5002541c0741d00301c48c04c0d500d041105a409070030200000003214091401c2c41d43c061b441d40001d51030765150000711540c07842170b208500e640c03110100320200e070400f641c480400341a412000c1400080902c08005403511a800c2c0004034a1014003035041d502c45c002d400412030100d00800b0740181c1001c51003482030380c082c01494181006403440c0503c850760b44681d605407260140c1581c1720200c80c4500441407a142c251102c0601c02e1005000700103660f54480d039881c0d4092400c1c81c4c046425180c140c84d05014000d1034000740885802d0036000b150030201c00361b520821780780c80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 355459433 1250 355458183 355458239
    0x19050406060509010527030102180f0402070213090302070e18010b09070e090901020d11040e011d01140307081f0f020a020a0f0305090301090809090f01141504030c 72
    0x95030003511a07115145016003c11418843e110388a0f503131036240c1a03210003c1941c0c24051b0400702c0020300b20392000901b02500581c0804100203414052100050740f00f09503030441c900780840e00000c0d0010740d000400c40b40203071141c09100425109106c25001007080c01681c1507941400c24600c41406c59410002c3c00c550f00e40b80900340140b820560140c000c401c5605d40240e111910018445c100c10b00038290a070543d02003101c0c480110041c800e40780d016103900f2142e9115401c01d849600c1c69201a406902c2c050126100303100c0c2c8030b00e4200e26904548050504c22513500b000d0000ca8100b610550240855024101e580b01c0038880350910404028540320b010405403030706410b000200e0141041c80c1c40140d01890310300c1c000695250009080c24040c0c01c1c110b0818141c00002030a4901c98a01105c2d018008201c0160034188280c0d040d8000c000780d21680520760412501143c11990413031090b02c64080c0c1c034800180030302c8040c22540916041641305604035106c4400d103000e165202c0031076031000e041d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 355460683 1250 355459433 355459439
    0x306040f061b0504090e120301080a0b0901060e0f07020a0f0605070f08100b0901210906050a140412050720090906040c0612020d020d0605090610170a060519050406 72
    0x600300c02c01d01c0801d02c0d4a649040c28104a403020042403401d4030303507450b48500902c0c082c1c12003111024500034107540c00281002c0f0342a142c00b80c80514050311060840e8140710042c050051035102c1d4583c0b202c69405400c2040d42c852a00300e02d4101d0f01003014114000c4405c0386800d100880d00f000340305205540740d5040800c8a410100c485040840702004003001c1400140110007071000285525001454100d40140c0c00070380f5084450f00c3c2c040e03100c04035582d400300c4a081060500032603511510303903e07040000309008507005074401c80040006041d0300e00ca410082006014105482515070880018805510324004844c03070003402c2105140300d004078000080c2c0c11007000440611039540102c1c10b01d0814942030041c0e46072100221450003154080c0a4007039100c0591029010701c2c8030005012802511307050a0144041c00036150714060b00081d6071b50410290001c06181840410b00b426040a81c0c8404001c4002e0040390400c0e5482504448070b510301a460039644030550320100e8007041801da03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 355461933 1250 355460683 355460711
    0x90510050f01020c06030c0d062402060105120a0b0903041a07020a05030c0d0308070c39050f2101060b1215011b021827010c1710050306040f06 63
    0x19910113165110800300002441148020050080364003241c1c3c0210701103450f207000c08880030010702c001188080203004180c110b54100a52030041c441610042e06049408103001c1d242c3c04c0c1044050030003103101c00401c078041d408008480050400351840b4144850701d084110144d8040c040580c4280c030320507004222072801040d0080304900040902d0003a482c2079400341d514120040410090002030f51081020503203842c1c407401e0b052049141150501e20a101108408503a030410700c0c55079038242000c1c805031700e90450850040000b244c454000c60444101818984024070584c40c56500385070000a0002030760307011b00401a0804034072009613841441c100b2444008ac07440b580040e4607210030050b20009000d401d240c185c00a04440c4140c1a891440204a40145d808003844c0030040b030092030745001003071500e407403284280083c44120380d1118000d101854805402c440a844180490010032501d00e0040c01000702800b40d803600e251605101c4000c100e0710109980c12818400d040e1220300c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 355463183 1250 355461933 355461943
    0x10605040e0d05031602010603021806120c090a18060c05090102190206090105030606161103120c1005060d0615092406030f020403170301080d2109020604090510050f0102 75
    0x9151079461900b161703100d070032070203605102e240c101055550314030000c409078a80da1000d840c00001d1680c40002818440d081c0b22961440b502d29a90070b406c80c6148a041d9070302e403629160443d001500106401d80d29500d0352082c03002c0464002c18151401464180740c035080301c082e1400d00400d800b5641c03c0055079141240401c644003009510003401c00c20030f203480d03000d840996044034025200758100b42030392007102950440c218040d607110100c0110b030000c40c60104024481d5280d0316546078106081c0031403c23030350b940300580a69200358840c1c00240385030b11500710744951241c1180061208994211060343e403081c050092282c0c5a0401d41e1581e2400c41610000342200c684508040d0810b2078104201e004100013580705500d40e80800000022aa001c4240a42e071404d802009a60b0f52400014a02d84401d400d07401041c0580c0c0041000812804207030802144c0a80c00301286584042c400142c81d071107160441450546408240420b07040300b082c1c89001d4400c10703641c804640c00b00c417005983c1c0e8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 355464433 1250 355463183 355463203
    0x16151403010b091c0609210302120a0c110a21030603051902060c2a0a1203050a1e02011b08090c0f21030309010501140a06110c03010509010605040e 65
    0x10b0307802084184902d0030f1880c1c4065841341c242400c004c01040c29620b02003500d0101c00c00b660509071429480045090002106040e240607040445c03030445460608451290028140010155590f4011005601400a04038110940d2046c3c1e0007004441c603004107040944020000400d010400040b100c2d4000d02c603000580350400002c1c0000d11000c040d11800c00205841240c03c42d802b0305c150b2880100821800528080e40250a02000004036440b881c8461401256106556503401007024044103423454603d9a00340ca0282d40e200340e043d90548180a03000d02d402081c0703400304291210030b503045d80b11425100e0824070b441040161100e0456540105564a8003281c000c0030741403c0d42d260005580c0c241d8034018110384400070556144010304828080c5070211034200100f044031210081c410b46001d080c2203016864505e8501010850f0f15a2501801c024402800689014000f003000b500c0103040d40100207205074501009400c2c007804c618803a02d40a1810011080040140800d0310980 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 355465683 1250 355464433 355464449
    0x40f051b030417190314012301020c100507110f0a2c041208090f06061201180b010f0f03050a030f030f0908041503020301050f1903080f120114211615140301 69
    0x2065811004201540c00c0121407103066129130140c10bd06134035218030503507000c072003621202c0e21000103081400714900c0c05000c1030300c05d44e1881c40d001001e50354011240d047d110b0b1105444c0711000c00c005041d1111400140c1c40450314010401c000c01c01600c45004400301840e650b42e11b1254448010903650f40b404110518015040070001611605001d0104907224661380004513513982c425030340191010001e90190340c600c00107001030061040c11110346005294044400f4005451a00c0d500e49034480d10400404003c2c00c2c82000003d9403180c2c100701150440c03050100706c6109249003c0310f280c0d1280c4030395880343e1b150303459113141d0034060f10907241214406482d12801c40310b12820400c90031918280c98840d02490703900400411843e0000d0141215016034450780c0320710342a1500703a04001607000c6060302070003484204040d100c4c1400c1c08021883c42c2011282c00c2001c000b09405c0052030780b041140d11340070410024461031058003405445901340c0700c242c2100000d11050180384800d010f0669 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 355466933 1250 355465683 355465709
    0x9030e0301180308091f02131703030f040c081605100e011b081e07060b0d051e0c030a0302010203040209010608010f0605070501110f09040f051b03041719031401 71
    0x480c4c00385000641c090009000d55000003001d50400e40d1003030780004007141c0d0350360204080821014075004800a40340c90b204c1030000b054950398040d0746c0e100c000c0000040f0708003a40404c3c200800ba00100c40540561000e48a070385a444141134820002403061600c1400100880d0034100d00072140304105005c10ba6440e000350390090000700c8400e0b22800c048481100c2004000724584060030000551000040001e40d184000d0070250262103101489520601003010b1a00000704001059140404400c1a00980b60521408641024240f1111702e03018081c3d0480f28080543c190300451089100321030405003a601c0b003100703c039041024010712800d184480703c144410f6000ba000f44c80300a102d01e0010030701c00c80d12090b1503d00e0700140110002a50b0120b80d060640c60140030300d41050001040c04c001b50f00e0416241c40c180d4803c148101d190100c0000810306002c05035900501140a00382c404d80ea03501c03009004040d4034465001140041d00d000010b030a0410b070110b42504039209003840760 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 355468183 1250 355466933 355466981
    0xf03110d18140d05011b0e1009140f0901060c020a0b130b0f09041104061101050c031b040b0f0319020f0a1b0218090106050307050315040317090109030e0301 69
    0x942d1440c20888030790019001d0204800a10300b40a000f0b5400403240308810000c1d00075201826988007094202d105065000110152039400300c491002c8403440b82410380e402c81440c0105107051360900c001508007810f80c3c00465420f800c05480f28100388282d501c00c220681c0e51b43c040ea0349001d020142103200b0a4080e003000009400c402034000c00b41480300035032400201c2e01c00907048803080f4442c0c480c110404141081f641c3d411811041440c19188024081c1c2e10307182c49040a240700003440317020f0803180320100e860440c55000c156400b800b00d07180d07915034480070311150701c0140d00300700c3e40c42c0128032000680c56610383d6940241c2d404074016402141c2049074214081d110750380c03401c0803a81c81503c2400f41d00c0c0980e0b40c0c0c0c00380c83c0c1c58641d607035443c450b6800d00c4019a825200c458101034001c1e4043c8030300300501c0e20b00040d14603003100c100c4a0030880341c80340c0c0fa049801c190300c4031009281074102d80c24450103080640c40b00701c44500c6919040000300411007070500b030b1012603004a00710303141751600b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 355469433 1250 355468183 355468199
    0x403020a09050c13180b37030b0a06081204080c1302070b0a0e07060306120803070201060e0c04050102060105010801030f060f0609140604060b03010f09180f03110d18 73
    0x3103600110840903441c10721844d00115a00d0a84a504c4048410319a10406044a50f0362180b00c80303040e8182c510381d05e080d213028414100b1649007614841e1041107184060741c1c22540740c00b40c03809982d00886c080100d0404100500140100d030148003528003d03920440d40e049804c42c125001c8031008005000095428400c00460000542c2c2c0280e200d43c0801c0f42e00e0000300714121240c4181c40d01c4000040075401c0d840010325200c03440d00203905040c41c0c14010b200c0090000115000d607688500700a560740d94081e802c07400340c205a8001283c0c0400e80e8240320ba100c8849024000351a03082e800c44107241e0346c5000444d507422080c40003403c00002c070000c2601107a81a000401030040202c0042110359a0b54000706c00c40b4203c94440c6052110401442007a103002d0199500411451141d503045505200034010f034400540f24040c6200e5450281b51102c8404445041c04a90002c1d440c18030403201d4100a090301e607030998075a03020701490307015540c070b00e004103035a605901c0d410f040c40c00b10a0800394a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 355470683 1250 355469433 355469441
    0x120307080a1a09041a01050616240615140f0301090207050c0a0906030501051b0a0f180e07030b040903020c04020c010b0d060615050c0d08060f0d030201020912030403020a09 76
    0x141d00d910329207000c0010344a07102c07840c03944d01580c0b10300110b9070b10f09028000040f20b18010b802152081804000003184000d00740355400718580c10a201300640e18415480d160300300900781c14220000d0500c00000b8001324469071500c1040300944403021648200b210740000c61050129950203401c1c04e20040c020035030f10341d0281c042c02e0302c21400c403513003645a000040c80864032a400607803940d44a0b407090040103001e0103607035007003030b4441603840c0c0319804c0403000c651602070b03641c800e020011021288110588549201724030400f407250350250785500e58122481e06002100c1e0940441d080c00e1904101d401c1c14820001201c1e0542c0c0a0318034000101f007044007940c480c1c0c0b610349082d929084408c4c0c0300c0c0c2d03e290222614610a00f0005402c61400300030161001c643e0140c14280300013400802c0c07145001251101b00c4544915001003144e4030340002541400003201444e0304401500e004104150b0158010f120000d0211803e03d0119544200c0c5640e038070031030100035084440380800304011240c40e04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 355471933 1250 355470683 355470701
    0x609120503041e1b0905071403012105160306022106030601030206131a0c0115061b1e050a0501180312020c0c150d0507080105090621030a030e120307080a 68
    0x51000c03450134441080c42110441d50044022144c3d1501481005600402400410424107a01da819036150030512407002070102e01c0540503040c1c3c42d1600d001c00100b8032460b00d00b00c0c441e0b0031003078107143c40307051070700094000e00700c0b05400b4825a1500036100c0c0c0da04480034810a00117000300a10b038216800d008840d003148556000e0400304800100b4464164001c0405403452640081e0700d642074060401d0941c2c511090408440b21158000e12101d41e00c4003040141000c21000f01c2e0022000d403500e00050031200854803a003100c049065806c000c004259105002d014030000d1002a074402a0100718001940004000c1200c030313241210345a0481e00980b0100710b80c80c05075100205041f0209010075480303c8180b038502c40c0014200c9654015202d59608002c440c0b0300103c0c650b040c1400b02d403442e0000307031130702d8403d641303020f185001204020b00680005407410141d984900c2d8030301c001340c0502000101a001e9000d80c001180030001030405503403044100b9500c40d00d403034482c01480d01c02411441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 355473183 1250 355471933 355471943
    0x7142205071d0f010f1e0c1b050604060f091206020910020d0c0212070e0711060a06060507021210023903040519080106030c0e130308010b09011b0609120503041e 71
    0x8054001c0d0b5101403619200c0b00150301c401c8407100e91f0340740401e039000e1110b54000343e6403840c0380140310a4580d071084c3c07400e0795110300f401a6840d00c0a0000e0b105000c055001000030000d29200504025051300138080c620403c1d09c5081c002d851120040e40c8604023910030fa40029180c9030050054030700b550040c07204c0c2c080300c0c060b40c00c082d41340d90380325055881c03c641102c0402c480f504000d0706c480082040b0760f44001502070400540c0d090280045c800d204081c2c0203032061510b00905071408170203201d810000e8800301d50031940c0b801b40d440b40b05042c00000c8540d05801e00b49074500e50500007401d80c44c00c51000d4640103075182c01d090000300b2010100520318103000d001d680f100410310403001d1090030301640c0110f55a420480ca01400c85240c101b00038210603880e4094640c0b0b00010340c125407402d056452081e0710540b604100c50040b01c80c0e034000860390300c3c10100040312009002030b950001d2002c901903c003c06400406c41c0c0d040e2101e2205a40082c10341512102901c0301c0c1d05d0901000264903ca2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 355474433 1250 355473183 355473197
    0x1e06020d140f0c010c1b0309120816030207050a05030a0b010e09031c06090e0f120306040207021806090705030903030c070807020316050307080f07142205071d0f010f 73
    0x4880b440e8540c0102603031010581d512690004066003210004101001102200019210aa6000b0120300ca2882800500c0c641c842c032510030011984151a01e00d8000c0443c091110b860f428020350365412407060b2400b0790303c0c0150110342401c0c0800c5081c0c046030010b010102030707480e000000300704080c01003140680d4001480101188061250030902c1e04035106c01c0468103d05016246003125505a503220655204044000c1c1c103060120755694050b948074441c035100e41da002c1c0420043d20034240000c0d031292100c04e031071301000ea410035114004d03401950f11100ca95a000410f540a1100b5103401086030b04c240005100d0142c600020170100d4411107075a8145541036022170715101002110707000c0c4030b122020074811030604200580080035000001d100c503000782e40c007294494089009a25003031107a5208028143c85940600340c070305d02258403105407440c85101070401002c094031501c2c0003489140d401840c5660048019a114200804804800305c0010041d100107041061840c18805c2c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 355475683 1250 355474433 355474447
    0xa0c0c080c0f10020309010c0503070807080a06082e180b060a09050112020909161406120c180109030b06010305180105070e031006080a0219030b0109061e06020d14 72
    0x10601405020f8070302400056207078104065024299254060b915042103c180708201e803980e44a1140e64202d202030800c040c903038840040c1c15020300764542044030140f00f040514000140100b2588451341c1c40a4074805c603031041303a040c150580c0c02d404101001d0440b00c038040d4000c285e841264540010004007000b80180c9e444014006031482684154500e00918000005504100e5080c0d94440d41070f002400c03070f80e120341062a01000b03840c050340c0305180180f081d0b4041a200c901c102c410030140d4035111021881d1080c03013101c159200381c401120015102d0705000d0154041d41000d81940d510500c000b90554410f00118010040140244051188401e640d103882c00c081c45458000c280540d18202c580403150141480d120001a95030000c03850004100040000810400d420b1903040740c00401c1c078018000070600700d4100b030700064000c5880c0c000005076403102e44d01000c12a004440c03003809601e0206040016044248602d80145e0400d2034440000391140d80140c1107091034040031030034281 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 355476933 1250 355475683 355475713
    0x100f0201180f06141b0d0b03030705060105011701061d0402072a270509100f05060111060405071a040e0408071106160b0c07060903080402090a0c0c080c 67
    0x1408010030b50720b04828015001c24403007103001d0b0f64040c02d980c404588050805030085100f002c0a1880207804d00408a4001c020009540250452510003000c80380c88005a040c52074036180c1c280305040c049000c0164840320b180c1d4a00d40c40d03040304d030162034210350034400345800146904800784042d8000d500b0010f20002811032020b540c840d00c40709a5950f446801c0c2284645513981540104e41d0301503c00f0240c1d05440c240441195800d00f00e010b002c84c0c0313a188c02040f24a45600b14000b85010360400283e1410010960702051003030500341e0320300c060b03021180d804907214803007601c005c0c0917600728071001d001c045142d810905050591038812032078a6a2407121002044007a2012980322100142d010305000180e051409a014104c5e8214545030050b84000d6070551801401819102080001000300d109202030b107400710b40041042c85030708820314004040080454049200c1c04038100464140080c0f4400c0e10003510719a120301d10b20a0142d246c42d541500b02c42c5003000340b882480941e40c40c00e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 355478183 1250 355476933 355476971
    0x12080a09030812190207020f131d0f06160e01030c091a040503010606030e03041203051614010507091a1b0d09180203040309091d06010b1314100f0201 66
    0xf1203e8240501c03507007054200b01c0c2d41005407a074600043c07401805032a02680c0e400880c081550f01c2100c40c0400e01d20a100c0c1500607200600c1c1810719007130701c07900e00100f618001c030b04802e08070003030810364545e6603489580080d040c60000e034601c006904044a081554041d601c0080c1c2030030304e410991052641c0f5084071090180c0c0842a48040d24041010031040c2002d01a1801071b181c42d003030501a00c0e441e22252a035a01543c4034040241e01c0500c2901d00f0306001d94204c1c0c0c0071680d8071004c00c50f0860315041c410070010580c001c0c002e4947ca40800104542d200300c80c20f9081d501140300d00f40304007002018130145034004980b0740c4401560f2002c06160740c0801c1000c00a0394410791036200741e582c1b41004403200d8054510b400b00f85180100b04000009920010482c00c0e10301c00403000035100152074018000603940b6070b1800040c840c600011421031240c401074541d0300310360003400303541c1a00ea403a2444e8040c41c2440240d04203c40b41810240d41b406000b5182400d403141c40009810150314007064000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 355479433 1250 355478183 355478197
    0x12031603140a0c20030a12020c0102070c260d0e1306140112020f0328061e08011104091d070303120e030316030c14040f0f0f12080a090308 61
    0x269903480c02c500c251034000c1181c00707241c0d01342e42021495240b92032140c4d849115660342d190800c16a0342210303081110a50541c0c0340c029003940215200d1045203040903407800e45014410510710f9001e041c40351880503441c1c41c0c800c0603086c0b0181040c81f40905068806914000800783d00c140c5c8504646140966841894010168807841101d42e41800001510706001c1036850070718503004001201d039100c0250200d036003200c18802c5482201d096220700b0102e074100c1d80f020b14002414460300055a11a030340c02407808000c840e10000507166104800c90032550b9140341044c04a030300340320822281e6844e41c0f00d003840f000580508075008220458460800b0780030b80084002c5080c0a6074101922650f200f100001c40c1000d00940c4ae6080203a031001c16488011200300c01c15072034040018a16200b8124038032091280001e081e03c9640f5212000c501440c640031303001b00311401d400c00203200080701d00d102c00ac8810181007400e040e10203480c5c04a55600014040f030a0001d650400000507042a00030211 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 355480683 1250 355479433 355479451
    0xd08030109051b0403030c0c090e0708070f0315020a11100f11090d0b0c04080706080411090103030801060507020604150c0201110c030d0507051011070c06021203160314 74
    0xa00d40c18507003a842180d601400c60320b0506071014520051030120000c85040d03030b0305401c008812a00a1400070380070401074001ca54000c0c10320040385a00c400028004050329808010345071450303180c154800c210303000c5d80700c00340c090f2a443c144200e03e001e407070707006041e0340e0450321340550450502e403145803a14250008403034840740c1c0c0703051500b4002024030a800311015003010303071840c04048100262040850003005040c0705901c0000c6854071321103034204d50040148a003681d00140e900d0501815030502241d0035117000301071800f03190044c42c20b40406410790360f154840315026400e00030304440c04c1d0001181241c001e0381c108004100c16002048285480080740c0e0f504000c00101c2c4001019198104004050355005000030b02c2c9950b00032a03032041c1c150151500035181d0f080c904005203819050030b0401c42491900c25442904c240d20001450303030900070444201c2c0b0513651001240c5e10500654a440640000c0c0b011449544108080c1c1c400b0300441d140118015a030504000c040c130f60701380d0306074007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 355481933 1250 355480683 355480687
    0x3151009151503060302090c0c150a0603111009150e04050c07060b0409050c040e1e0a1a06030307060b0414071211040806070f2601170c0a0b0a09050d08 67
    0x4550501e003042c0c269201810b160a0003c6407441e40444c00b41400070381420003208010a00209100c01089041e003a0420710300d4109407828103c47d4031740140124001a58200d10800500c400c5041c1108036100c40340c1c41d60346100c9454605120300300410462400c1d202040310703105840c20b03982c1e41c03405030900a5920103412640c1e000103240040480304290061405242049401404550301141e91080103009503808500d031080102d2481c101075406c49510507040350040242400480022010a054130a00c0c07000c0c00004040300c0303109500c2c811105194964002c104020002c2c83c10b411142c00d42401400c040340c5034804110201440804a41e03002c006262940d003030002016a006554008651a080c94039107405c00000c291103810003031200c0144590a000e202c0703210301c46c403101d010f001e18041c1c40500707107541d02341030501c0a1420302c12480300c421801a01105144081000001d2280003010409618a01178440405401c9540200280040758000007480e80324110f105000505c2062015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 355483183 1250 355481933 355481939
    0x40c0b0c07140d03020c010e040623010809190219170c1017060d0c03051b01021006050d0b090c03030f130602010225081603020303100605090315100915 67
    0x80a0b424803039990070301c650a0302001c0360209801080c41440c80700c0c00e00c5c06104004a480206d005081140d0041d42440b8404481d090380e031018002d0042c0d0040241d0300c401154a41148907561804800c7c040d400c680080f40040d1f00610302401c1c40c9100350b0512010304101681d4240a05502010008140442e001401c500c1041d280c04058010140000c4c00c0c60201d60300551342c101c2400c1030051440340120401100340d0144513255030f14500943d4000d0840e6111b801304901e00e80c80c80c100034401c0b4058070400d11040142400d9018407820f54002a00881e5941c885427100f0000d8800503103441c10760302840758803150b1914248010500d441e00c2003812551034020010048048543d58004030443e4814040001c0070071030002800e00010290041640c48102c1d81009021481001c0c0100500c147c01c0c00e0503002c0540100186200740030700c1600c03c01c0d0302c0e03448800341c50034030500c1c40c0642e00d50032000c540150301410400d450b03005032035007103510412030b01c4804034021502c4100c0c15410000415000b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 355484433 1250 355483183 355483199
    0x92406080f0702012f161208130f03050912070b0405030601081626010203010608010306050a091e060e03070302060103170c0a0602070305090d0b0615030402090a05040c0b0c07 77
    0x1154102110f44002c001c03600c0c050600c0840001882c1c0c20302c0c29400300038043c0f520003414000303490481d48280040c081a5115203801c80d00341c0c5414070a1004030f0b18100020321004416000040d246410000c0c5181418603a0380c22030701d07a4031026495134090920841d1314110081002280701070b00e15000120394950400041600d0010705a1001c03949622065036040f6003110303220040110b03030902c0301d45858041c00328510742c269108115000c00301c0d0700c003000000d1500da200042c18100c4c0c0c000c8200300666180c100313041058a06c00e51b0003800c41004c50303041d00ea80003110030072440b41c14080c010005002c001c0380c0d8420700f15844000290300607401100140140000d40c520f240c4088800b41d55546401c80507240f058540d910352390301608480c1d01140c03000605002d5002c40d90842401080117002804500d06204104070540f003060080e180d1001d406070303034068030080307030b019940003000f603611555070004900c058840144100e40c00500d00c0d2000400541e000007422442d00c4d00000303070030345504002c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 355485683 1250 355484433 355484461
    0x21051b01020403050d050c0a0602180a15020a030503060402070804031101030b09090a03140d0f090308010b0702240f0c0703110906060a03050601090b070807060b010e030709240608 79
    0x46412103900c10041000000c9000580340031500903410b095407142030032254142068005c48001e0005800042c1e012410a941803415028120481d065001a911003031205207003c4c08904c29070150744480c042c3c80c04240200040c580c4203c1c014000361a201d00c03551135a1480c0c2150f441201c900840e000803504540e058090481a40020f845221540c6400c00d4030681c2c5000a8501405000a006a6144102c0c40c50225489110502c001380030405100508800400ca0b41909400107000382002244400c0200101c1740a9500100304494410800072104201154120b4568180204109115602e072082d400f40c0b140c0b50500c1d01600b94507265003002c80007802c1c0840c40d5481090040100030781d0759155425100f9400c3e0b60b01d000506036032030a0060f81e04c90416001250a240081070200c00c104000c1c0017450724074411182440301d078540500650399440c50003020359050700040c600340304d122640d9002106e0640451250140f00f40820b20014950840f81c100a001440b03400c00c000090011540c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 355486933 1250 355485683 355485727
    0x306040b040912030906060f120c1737200d0201050a030923070f050603040807030f0c08191b12180e0901050601020609010612020402072105 62
    0x7018040b55489a81e21520001100030400c10301d940c3d07500035810b008060380100084c0140b2120590219220082620909107488040300c00d032003850b0000c55164034035800048600340680c0104500041022103902240b010000c2c104418201c900301c4e240d12224100420ba014012840c003031f9003200c0744d440011001c1803030251078000c4446102807001030340e10408903400781a59140002c2c640c00c1900d083e2640408071282400f2445402501c80e08229011440c101143d00c280118008550340b00123101c500d0100701c4000c0c1441070140302c500c002c64000c00d8050401081464508000700140d81c46c9855030300100e12403500381d0881e2803156015500150126040307000700b05010030801c4142c0e01d00694a0900000b03d040014003003d41c1c0e503c0301100700300000350134010409101440c210803854000d02c400c0320014010302c10000032130160401032140c0e03000d8908030000c0070b855900c55024070020f5840078004031090071200070a025021030000510007100038540d01d01c0c0e9211803080002444181003c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 355488183 1250 355486933 355486939
    0x20f0d0519090f060503060402070c0e1909020306040b09100504261e090301020405031005040b060d0302070311061c0903021216140a02060c01090506010f060e0405090c0d080306040b 80
    0x6824070030a40883e00100840e505858161307940e60b241070108000e8016110028a942d9a03500040f40c0002e142c1c802911512880140008064403182004181e815545002e0741542094001c140400d110203000c03607002080900b15000c0b0071140202c2070071914111070907204c030284e07034610858a8241c1c45913400b542c200d101049060411407640b1180c09503049190034401000010500c40c1a28207405071001041c0050645120703110003151007001e464122002c440034201000050414074200e1054607000d5010741c000d12119040d0b5031100c4001d408401c40b16031202062104c1005601e4610300c0d132100c41c10711540425032540d80d20f80681391501220300c12852041c00d0284001c40844040c00c00f50b0950031059014a082401c00d004c0e0606078a541d01075000b1100150700300c0100d10540100c0801e9104204844060382d807200e001c41c0ca20090302881001800081c41c101942c5420b8003c1c076001b100e25030a50306507211500c00104503400f05802261255804020000c10f46410300c02c0318003008090b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 355489433 1250 355488183 355488197
    0x90b090c041407021f0e0307150e150a0c09030c0b3604090204020d06030f12030c0504030303090c050405160206100303052203080708040305160f15020f0d0519 70
    0x303e4070180d01d9200d00071840d0a90208500a0074540d10315420180c02d08940c5400e4a944480c64241400340310b5a41078181e18030380c2404902c6500402c00110146031200400350111a9100d40f91030704c010b460740420709800c1140c21240407010460108620f03004002c40c03000581e032961100d1801c0c40343c1d1224804110980f0b4000504500c80c1500b50007525605c2c0d040b200041c00c0700c1c107440054020b01901022801442c07501201000300b20020402c040e07960700070b202e8500d0261401000710700741e508040c880340c00100c0600003000000d00a03003100f01001d200341190b8140941b2107001c41c0c129001280d000f0b0455490301018442a40c050051980050040c03055180d41804d40c1c80142041c031403100a01100b2401e2128120851803c054040181d0703804801d131555100141800c1000c0d070030a0006803041d000711100c0000ea488456180ca04413654a01042d00d0b9074600b44248010f251804402c40c1980241d040400c040501402007514568a60f00c5564032099840040116154504001000e001d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 355490683 1250 355489433 355489441
    0x4090b0907030614041e0903170a060b070b131203051b04080312101e0e071d04020a030e0303090f0c010f050f071e05060612071208070204090b090c0414 67
    0x8813212480100c00c19100428000742007a58000c4c5401a01ca40304222460450240105603008010540c11500203050b5103207910741c20102d0342181c2c40c034400c0d140c08000400854002840c1c0e607813420741c0668061084130b0f10801c1500ca090802d04040003000000c0c0e030b158100607080c113100020f03981d064104140c190a09082c1041c01d603691044103200030249034400005942c1f000c2d401e0052000d404610801d03240800010305001030003c09000300000b0b1802c903c0000c110360700c280c545400034000c14401211091540060000940c400c0c8410360801d0344640c0b0826203080100020345c0a00e4100d00100b010f40c002501850410100048a9042111900400c0015035000c4107075140340c0b483d20119a80d0f180e952402d881008151544c50440d07501310420030050010100c1c40600c10902524100031002e464a055a281d00d140d004404000e10001031a8001c142e40002602c2986d00c054000036600342030713845000780c2c008212142203980e403000ca1048071508040c054505a0108030107070b408c003820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 355491933 1250 355490683 355490699
    0x302030106060c05060c131212080610020318060f070f060e0c100311091e0102070f05131d15011e0f0b07060906050c07020f03031603110705030304090b09070306 71
    0x1d0f11200b40c00801103120390703055126003540c1c0300500c808001c44184018a16100b401245480e07072718000304103000d00150090800020b02407014a40b40c2c055440c002120000b4200c1c81e1a40e40701c1600540140508480e00705000020079520f0b02610100c07101d4003a501d00a030036541101d8221100b600003c1c450710054a9207241c4c20740e240518103000c9041c1c100c01000c0d80c0103014000001c2c0d0300a14000e00d41d0032600c11200042c1d9a1a82030703003501c0c00b0b5a10350b035940c03040005034481c440c0c21464200846001543c25400740e044003a241d25904a00c2040c8544540760080344d2072110440380c0715200402240d90050301101041025591198a1524000016010480034420101340b0304e40051003e0401c10107912078011158030001c01c001c68180030f00c080580b83c020714400c82c010035410f00c2520191030000241c03940c0b0b06810381c42d1041005150707400c44641c054511060301920031004080340c261341c14406400540b90140300012880c20400c1001399a880c080c0c0050b040c18030b400d01c01e0010036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 355493183 1250 355491933 355491943
    0x60e0c040506090907020c040c0309140c06042907050102040524040e250f2006060f01020a08030910060909020306040204020a020705041515180302011b1b0302030106060c05 76
    0x4181104c03031081c95642c0440c141d040c1a14000e48a51003440c0811810032140c16a00500d0818080d0101c55000e095902c905540c3c0c0a41c140811381c4523005000c100100c10030210a42c00188034103005d0081d03500c0d4a00b00c45100d81180b00c040f1050794001c6014055428211070f140c8143c079422400c0803810b0588801902903200e1402a5801e40c000480007544401341000c4014099004000e4a840d42e9942c0e0b40042c88103088520003000100b49108450b400c03041090042440c00b44140502600e489003010004c0d01c1d074000c3c1e031460540c0941c410410218034450301451041052602a225002d1041240000c840d416000102804e141c042c0100260324002072590748564151001642c59108041c160b1074100540d000179841402c1426003501845000c0018044400b085030010494503240001d85550020340e901001d80016442d04102540c0300700f0481d0800c1c000c080c00c2c0981c460054444d41051400c601110128180d0f0740c07000c00841c02e00340309840c01000240381c03007400e42840756101501c403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 355494433 1250 355493183 355493197
    0x191e0305091318050c131103010909050f0d02010b040c03060b18040b1e09060307050d030e0118060309021809030a0c1110210504081b100c0201060e0c040506 69
    0x14000c50118090481010741c0502c0c0110303104590110244118a801561201910b103403074020b90804504006c001c02602803004500c490700d00c0c0e14150313170030a1419001400041003e0718140706840f5007002c2d02d8801d01180c815620503500110314552800284030507110b0710302e00700d8109482c03e0000c111407c810702c142c403418000c6031642e0456441e0540054050300c111000258000d0f14070351403100883c0000816219107100313444000c0035568050400d0384611048c80391070f40007903661418a000038071401040e240e102c4e0504041504444800244500101c20f03000500407070b0780d558207a019171500e0100c5071000c102281d0301032480d1415000312520b90094160300001d201d01641450100060402d40030000103000c0c004c150300c040441d41c02000d5a18030032240c0c5074500070000e102e55503178107409060310807600031082a00d04011440c150510180007003070a103d9015a24545100e480d040c010180380d2000d41d0f0012031810b0a03c01d042c18400006410001c3d4a04104400c010a0315510709540b24 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 355495683 1250 355494433 355494439
    0x1e04081209010815041b050403020f191a0c0105180616090b0a02010605030a1b0b1e07050114070f111b0d020102070b0d0213050d240b03191e030509 65
    0x150a022130110b405400640000010f2050748995643d505d41e100002d0402c4074004c41e50480160716101c240703e401d00700c1042c062403a1902c04004c0c4040c0038400030180500e40300540442c9804004640f550171100e054445101c00d1140712110400031808018640d009040b1000820301714a12043c054107040052040303107004100410190743c000e0003940180d0050102400b9034080e410640760500030818001c40440c1c202c0c1c451400807070584064420b071050740e028910070403c0541d402c010103055400c000c40480d8a5034842003001211801d01c0c0c0301e28021510350b01c643c00a001031000103442c140d500c0b645601180d2005022000d158100490f45032801c00940d28410f8001840c00101d0500107503401403100314100152804035080903500a0840c1d009880c40019900e82754810009040c000f001c02610420300ea920320740300c02082d8605110481140740d030005009006070042030410301da103080010f401c40c94441c54400d104003110082c009440d40c04501c1d0b007204550b0740c01340c128003c070340e10940 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 355496933 1250 355495683 355495711
    0x130f15170703180203060103080405030d02071d04061b0f081f050f040e0601060c1104020901050306040e070801060303020c040c08010501140a0e1e01120b0a030f05031e040812090108 80
    0xd102c8500b122505041500542a1b502c03a60b146e06200d20103600900ca40e80c080d01c290305a4458171480455088207603034403a080c050081f01085008408000040d01c20f071401a600c0962140c4503101101c1001d40e08565209d0304200b403920710018046050081010740180807096101c4030b00c2c04440c242c0710a40300c08071140741892003c0b1011400810315601040618852000046112904540b4401c40303d4814102048044090b01c2440164025144140e02040382400840d80347e107002e4105500c1000120108c3e0540e560300e51007607080d50050741c03095025820154214003a0b00341800751001380205410200f410b0f51400c000205891200300d419145100003007208041280f0891864110580060020b480c4a80d0311200000d41d0040403211400b0403015500f001ca5030413640600c0b0101000109803825641c51502c52000350b490b4010200c8490104100d005000c144000c8220901001444140c1c0c540c0c4c10304a0051501c21074100d440c0c0080000c2c490140c0c641e0b4041091035005c0c80ea448800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 355498183 1250 355496933 355496951
    0x212040c0501410a1106250309050a020a060c0c051002030703051c110c160b0a1b0c0b03041202030c0318031504061a010e0d0b0606130f15170703 64
    0x1c9a0740030912052402140000c2013600154861004c011008140341580d2403030f2522030314103040c24a03c40ca00062055030b0580e440107d80203500242403240100f06840d00c2c3c90480c0d0002c3e0031801c51743c00100104449002a1080c00b420041c994040c000075030368280c500c0c0340c914001e0b60341e000302c14004041200008141c4446c004144074540450385c40740041c8a480e8034104030a40640100389254102d119109004103c03152002054046840d8031480610b440c0140c041280c0001c5001d200e541c01340a540c1c1c00c000001c010819450003820b0000103103890b030411303150140441c1340c0f0642190440d417003441100690304d00401210446000c80d0004c04400a5820100342401502180a07a41c00b600104000600205070420a509490552a0b1070112000c1c03005461031001070607800d811001c1344800d11300056001c8040b0360040c600816450070000c5510412116002c0c030b402c400011008940304012038034030000080d0411445040c58038500c151001c0515009800421078010592108242 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 355499433 1250 355498183 355498277
    0xe0703170f03090304060f050901080103030f030e0f0304060311190e04060503010c0201090308060414040825060608070905190f020c12070203150108030720040212040c0501 76
    0xc070010100c1c07141464980c0381880c4003540703075041072150001050715010080e0110307103d0022600b800005842c0c3c810b5607405c507241102d0300203601c160303d0141a5540580e01c1d0700341040004c41041201031005580c1c030703824010001c0c02d440e0344181070003490005000c0e1002c81103c070000d03a17941603a285440000070f08014001009820107920041d015483c050300d030f2010720342c10b42140c0490340c025140c00c01a80c0b590b40500c0101c808455200798010349400c0443c00182900c001001c0000c00c07550010706240d08915290703840407804108844907560345004200160040c0582801000320086c1080240f40008080407105c10102c0f214102c103940704201c10900d0f04680c1075920200a00b8216680c0c44500212448580e00045050344280715042c0541c00501000720002c1c10b840641020f5800d002003980d4020030150200e41d9014a081810102c80301c1c2c0c0c0361480a0200b5200040f0395050b41c1c105070a04051361031301da4219a0410180e181e2030724443e003281e00b0344046c001100b5185d880c0075400c0380078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 355500683 1250 355499433 355499437
    0x706080a09031202030924100b03060310050c0d050c09010e19090c18050a05180403090803030406050a1401050120030d020301080a150c0206042406090501180e070317 73
    0x1500c3c40031440407040c005421400109502406003581d0144070070b0315040546d21180108030b0308020600f0341c0c1d10081c00310603101c4001d95080100502101e0142030203c54600035110101c80c040301103000440c03400a8039010b03008550f08032110030005480c20341008002401c144118074054018070040015001e030301840500c0e00000c0000c2d038020015a00066402400c0074a00d415850040a80b02c4001c9450701e4070601080485000501e0211070215900704184045c40080c010740600c0010b1400144030030043c001035104a104010004d103500d8010110421107000d11240b0854001100040c0202d90b0461200b004a0a5254202c050803213601c1c60103166200b2004480000c1d8000b100001e841d100004482e40d03454800c001040b00801e90302e180f001150b01d000503480c0181e00c81808540030811603a4011400e1550b802064084440000f040d015a4440d6100301c80729035803a0b00400c14112200080c07044d0351941c1c0382c04e1200101103603002d5911142400b01070041d00307070214010100750b44401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 355501933 1250 355500683 355500707
    0x5091005090d32010506041a13050903070c0e040b01150e01050c010b060c030403050d020a080f0f0405032409070803030c0d02091201093305060105390706080a0903 72
    0x1c65010521002d03d6142d0192005803101400741d420324000010001e92390380d070492480405841d12400c02c400d40ea10201a007806000c04081d80003c002500200d00d404502e81c010b091025213410150a00b49000400810140d220196010003a030122281991084240c60a90800d00c1c1c00c5885a240c00c020600400440106592080f00081c20004c000c401101810480c0e010f241900e21070100c4034801d0741c90b440c00c2400180000c20070800b0341e0601001c403014140b00d5007140906400c0c180c850b800b092400200d04220668080d051401c400421517041440c2e07400903401015100c0c1520b00b56a465503804080c210081c103441c0440d1202c0302c520a641500c40c40c0720020000b0100c0b6814140703540c02002100c0c0203503581074080b81101c0b40c08908289240f43c600341e0701030040911080300e400500408000c1c206a0422100f0000e0082c00c03204202102a001440c50f8900c2010503000e502c400e42c3c5503400d000340141d4015074070800020f80c004101541c0028002c002140d4000035140c11550081490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 355503183 1250 355501933 355502003
    0xe0907030f230915070f02070f09140703060501050904090524041b0302150309150a0b0108160c0f05030903030301090605130902060306012003040605091005090d 71
    0x74015448501c0c10b00300304410341d4200c8500180c0f81c56654060303442d540803542c0e8040066840b000700320300034401ea14400500f07110780305441e83c1d00d4a807085403a0180e000d502c1000e6003501c1e40c90203041c0584101125410810380d0a0400000d8a0321001a059000d02c06440d44075540e603810000034088244400f02d0380d01040c9040c0c045480700111400501c0d4001d0303034181d5019514083c01300a20008804200075070303030014402da002c480c0500d060841603000031b2034903556020302c5c0c6c4040d04c03510f2000e01480c020b4004400114010305004001032685600914044c0720400d003540804030b06410001020680e5040f00110442c04450305000e0701d1440390b902800d4143c4400000090400c42035030088040e0b540498441d1440d109403010001540e02d06100039600c5103003040840d840f580a042c290304801c8031220381c415003220340c1c01c101e421600181c0c4000041380b00000d180c0c0ca40c0c90710b14100070040f11141007003800e10400d0000b00303d2031040b0500050454001d042c40140074080070700880401000f803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 355504433 1250 355503183 355503191
    0x30304033c080405060c0124180b1c0f0b070e0103060b070c14030708120304062d0207060b0301050901060302030f0120030c04030c0e0609010b07030e0907030f 70
    0x880c03800c418102805074991000c840700d1111a064090380e604850030150003858a5061504000401a44d58012050340c081c1e9036032403481ca2099200901d41800f00a410003912020503d020401700350070844540b85080140361040360803150765010031440e2100003800150b1075004043ca800d20030302c07070340031005418612680c040000f00ba80c0304d42c18507644030080c4d030b0a110303076075907203e6050312400307200c50080c08800c0410040c44060003541560351208001001c9070700d074980d038124050034401002d480c00300a400002c00c01c024400c2d10300034481100f00707141ca00c5855489081040c500d801c240540c05101d1500044c82600b484080d41143c00e809034001c001304110b00b40720401354001c00d00ca101c00c80c003e01071688113240701c96040c170605001c07a20440c0112000c071090b05100d811640020107002c00480e0078400440821904020880030f40030001415030f440c00c0403c104154180140d200c507501c45c20400010000a51003408600da1a00a460505090301c1c3c211007980600a10542e030310300b092030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 355505683 1250 355504433 355504463
    0x903020a0f150809030a0f021903020106030506010503030702011d0f090a090201020f030f0a14040b040315060b0a050a0f170a02041703031b0313080a1d0d0b010504020903030403 78
    0x40300c04802241c070b403003800d004a09a1035400341d84078507040300d0381d0103190070502c14194a1400f5211060086615106691421080c030050940b1a03258240c10340050b0340d40e220520400800700101405010210001c60030003000b0b42c0001c1c41002490b5000c18600740510500495495118002c07a1540004191240c00d10340b401001000344044041130703005114819100000704c601204a4110354240c144407494514058070642c1c40801e51040d8001c0d0f001c00b0030001a42c034a041c0081c00145100c0c0c040440b0b4061a02600820360707509030002c280c0858100032140d01c141d085400c80c0d80d4034540b030420382d0309116822010703030f0008011411200c40c40545c0c402c0111074903e9030300030070981e040c0380a0009021030074500d082e902c0c0000c40d542d01c0094600d615400308980444051a84510700b28107041b1111a25603da04154000510ac000800c44504401c8600ba01c55110712413442d105844803d6a180c99031112080818103100d45801141d000414000b5038800342304680c051a00901140b0650764 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 355506933 1250 355505683 355505699
    0x120209012c011212080c09040c02070305151006171803090301110c07060e09060906150d0606080106020f070603020d0e240108030c12030a2306030f0f1b010903020a 72
    0x143c901c001c50b900d400280e207413000b1500605e5028040c582d02d80b0501d040038188010700c0000e04440c1010b4003988070b94200000080c40400010791034a1108441c0c40c020b080070100c1010300e1440740c100e0001d000303050440308c0490b40c6c2d0701c00c0542e0124440c100c10109113030009607103003148181091540c0550030421604030800b8140d000b06982c50490045964030741c1d03901070883c0e240c030009210960004038000403c101d461300c0d1000d00e4102600a1080107852002c44600c1000c0d8005c06403801490340f640c10412200303070408003940c01080540050400b00807280322458813a10329000342e41c2419030214032000d281a244c0d00c40701c8016000c0003140c6090408031040080800b600c400e5061801182001040c1e00a000c0250f8801d541218010030400400082421031500300409000300e55a07503403038204804012412208681c95000c00346405801c010040c0342c14284d8401d40c0004035403210400d00348410300046d00d0780700d22802002044101080c140103c4000710769a0001e507110f42510300104c4c60761 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 355508183 1250 355506933 355506959
    0xe030c1504110d0b2403120d1401151b02032a0402040b03061e011b0615031202010e1606050d06150216090507050306040207020d0c1202010306120209012c01 69
    0x103034484035a25281000c2d0f080b07020300305c4200268150190002d1648642208010700070781500040054040740509010031f8800d6080b03000d90000d048913584856840091760000c60040000d1103000660900c054150017082c1c0e1071207050086064a01e28090b0004510340b01e80c0c0705280700728020700c02d568507aa140c0d41400980c00580b4814410300d4491085180c525490381c40c1d03c144801a1510a15044601800348480c010380343c099030711545850851546054404100c1c0c095481018041c0100d058054000d08554000d4401002a4041110411840240340308141100e0003450169135480307403020090054000f40c1e02c02d08000704040703520a2600e07004114100110b0780e400024040030b95441c401c9007552401c3d1218408a1010008904281003927002445003d00141c0415034024007996104840f04a07079000c410714851404c8610219a1300d0701885009210003510350380c141c005500010440403043c494149180030552102601200e190030400f050070070324245042c0f40da591001c0078142 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 355509433 1250 355508183 355508191
    0x40e0615180a1403070e0c04031b06020115080309060d0f02131d0103030909091a01081e0c0901050405040c0816030606060807080705090310060b0403060e030c1504110d0b 75
    0x56800700b030002c10000700284800c041003800030024426149495070b0407041c3c3c10081c00d400220102000080089011160075642d61500c0720b0f1424200b0b071a0847c024216110750b06850340745c81c04203004001d49500041038030b5281204a684e0750b591014105101d000303186030391300e0070b00080c00807603141c2d4003400c1a038841c0d084400004c20f80d070010140e4407410019050900000700401c003022002e00201080e54400c0401c24480d00511801c0103800610b040c211100340d01c000d001d540521183c0e840204910003803070349191400010301d0b440000c0c400152052505002e1240030341d1f030344c00004060043d404c400c0b500400d250f50a0b2144028440d583c070070121118001545c2036410b180d00080c141d072144078000d1107a040390b6a2641681c407059821201d0358480210194140f0500c850300e40ca5070b0744c80c8200401030200d031881c02d595502d1351401200340c400201e040803007038009001c94055940c3c0854058038040341032013081c0e0700303580e10302c1d01400f03d43c150784c2c80c6604088501949004c1080120b40b00e805 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 355510683 1250 355509433 355509439
    0x306011b11180709122a080106080f150406020708030a0209210a020d030302130b04180e030d0f0908030a0902010818030d020c1203070207090506010201060605040e061518 75
    0x40c0036003840001e03242c00400e4071a00f0001c0d00da54410001480c0d0a8651140c607441980404400140c8080003a007070402c403141b15039107401c100001c100c0d5a0092040740018441d04001c2c5c000c00c00d01c1e66803030f40c80301c900e0100c05100740c5c807100c0050100403155040b62201035210800e46e481e800d0110840000303401120b0140d000f00d0f088085485c10600d500c0e08440c07031440040c014110f40746150b003070041d5000d20b0a002c40c107143e000d000d01d8120800e91034250002c4c100e0b8181040c0c89610305040040a2852075121881040c1340050040c50350700d000c03044551030905144049820002030500718014010300001505108000c018459482800d410402c0038038000d982c0d00781e0f541c803401b00705180b0903044400c4e160749034020000211601856005420030352065020345491060180041072654000c540600060304000c1d0144640c03607840c451a500000280700800010741040e1001d071891059005101103102102d0008140d0794404070005a9850114071017912025402609583d102c403047c50300784 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 355511933 1250 355510683 355510699
    0x51c180b0a05010f0b1804050915060a060206180f0d0504050f090919080d0c0905130b03070603110d060b0903070b07080f07050f0604150509061b0306011b11 69
    0x10540d070740707400b8070340c1030300c0002c40b00c9000e1515010142c440d540c01490003809035681c083ca0024240d4441c07007214800ca948502500d4118140d645900302108003c10b80c0703200300b813020401d120980d4002042607106960807400f01c51308401c550864034010308520202100d01c05c51034103000665000c800340c41150002ea80c0c1501180228003040011340007207440c3d548a07071100141c0740700e000550b1056280c05001d00a41c80c906011045810b0a85018110200120b00781180400040c01c1a030407a00c01c1c041d8958081040304600300001e9100d40052240004043d21150307003c0e9100c605104480703840f2900c03403040000940d40d54a04200c0d03004074880380c0c46401a448002440c540c184101e0350360303e51210303119141c406500304003c00307500030b101c080d41c0c0d61060785901b2031380d0382c0c0801000c0d0289004401c18907500c445900342500b91200201040040e0700154107115241c0000350400350b161500d07407803c80e01caa031070380f0040f030b12000b200a48420041d800041c21f03050041d80c8560300414038007550104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 355513183 1250 355511933 355511941
    0x905071502010b2404050d0b0103050c030a0b0601120e16050102120a0203070f050c090f0a23041202121303020f0303091e130c020d0905120a03051c180b 67
    0x1a003260f4140c8001ca401000004011a800046059101c4c034040d0051540f4206501c680120341900410b901c12680880c0da0030051040c04030070400c107980d80104600070103400c006aa981a2154009440079040c01107426441d6584200c1e0741141c4212804541210480c845038001d4040b5448540308550140c028009200f01892800c0c04481000c80207400030741c40c00000e5554442c45080a00c820b81d942d004e0a0b9008003281c2c0c0314407116010380c84811044a040c148101031200300d56850000c0000288041d0410910441031440e09a00c1500400d1007414000414001d9003820500300896000c000000340100e0350341c02c00e481240680f4000d4528500071084c88042c95900c1c41811012a40f280c00c540900078502d40040c84c0700400324000c3c2c201c0c01d401548080310350581e12078100c28000b5030002100481615401040c5038010002220100c000002400e9120b840704a240e001408000340041c0e0070018042c91240e0042040610300e041120a0000c58028003104003403400b16014142c40000c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 355514433 1250 355513183 355513187
    0x5090409020909010911091e1302090103030804031b0210030c090509010b1e04240306050306010b0909060a0b09010c06060317070b07050c0d2a060e010b03011a0f060403050109050715 80
    0xe0388120184a8460003c0003020f850340641a002050482400d49c003a40020040e140c2201d04c5008600c2078072a6110b9040526015054a207110201d01417500303000c1942001d039840c0b0034010205022800e001441c00341c51042183c4400c002c0e006550170601050002590403210802840c1210020424071040c403035520648071203100d40d2241d449085d1024280240401c050001e4003070005040c240050400e80e03a4001c43d05028099201c1704c492580413a400a6500700083d031150700120464001040300d0034a44805214060780c5603550401c01244140c0080106541c4003034091030b0484a08800c104805c00078150700d5000440482c0c0b07154004000c113025a0042d030a4811034a400c4014110441804404403444010424000c04602105c010300c802000c4c0d100e00f86181c1402120302140580f20400410309450300d161419002c0e81c50300c1c48a000b240c0000f904c1d1810100115004070710345800d400024403901640e040a0195440c100c254400c014001811781c0495000d11034244100c40c0b01902 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 355515683 1250 355514433 355514449
    0x120a030e0613020f01020f01050106050a11010e10050c07061406010f020d08010302010305071709010603030e01020a020109050405090c03060901050f060f100305062205011e030206040605090409020909010911 91
    0x6040392044071550350400514112001209513241071048502403485040300c0c40c29034100703a00400125400241056415070b100a420f4490640301000b405400c640c00c43c80c581d102c0680c540300c40c11907580d0000c14100c102c070740119030020f07801c54020720401c10400000c2c02d014a00381c8585000c181003402d00c500d10390000c96680204e00d1a0703290300f50b00d81c0c41c1d5001900600320042c90101042a00c450000c00c0b01401d42d142030180c2507a00000503983d05510b8042c1541a510000c02d0541d03020500d44801030b039220001c03000341c030380c01d5502051039180c000f1000d10b030a081c92403941c2d1500403d420015202c0055114034803a264500c154102511b9040074044100b180d108180d8004010160560905010390003541d00840702400d0fa00900143e85a1040c040c142c4d1070601880548500040204d814a840b2000740705202c0d00200041510f1035000426078072840c49080c0c1030103c0490a10f8441d6100e61140792002d40140484089280010456000f8a40d085040720000c80a0440700c6d014240390321 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 355516933 1250 355515683 355515691
    0x120908041412030301031b09090f03120209060d20071410090b060118030b1317090d14160905010501032315030a060c170a090209070302090d05120a030e06 68
    0xb010b5440c2d6425a1030f0141d40040251102d858203480020024004010340300302e81c0ca4502030000701c40d0b4182640f034020001484544580e00e410b0051240324125036992080b01e203c8004580001343c29071a013080300c8401d20f8000f14101c06840013080d05070600280c0c880300380c0640c0c0c10320184e0301254203500c102811511002c8014003001d5113003001403460350003030400c0386c0b208c58142c042c290303200d9480e80c803280300c150201c4608410a00540710101040042c1c1c1e0107500450030f00304418105503030780c03000c41d0142a6460001d001c0c0000034200c2543c10074140b01c40400d048080c0b0150301c04507141c4180078003038030080c4909030020b4074002c11196110558041b440c640249060300e60643d071030340102c0f010766011001d04140c0c10b00a0034003c4001a101d0702c15070000c2c031040d84a0881d0380c000c0005903008240b0003801002c5807070070540094011707a642054164884c040d8100141c803148901c0104200ca031142e00d0081c00f92041440d00381e4031102140c05010001401e58091088010601f80940c640304191 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 355518183 1250 355516933 355516969
    0xe07020606012a060209030c0a08060402062b060302010915080c0a021e0a022b030810030f051005100b040b090111030d050103050c040c120c1209080414 67
    0x40388503584034a42580550071220101a031003401c41d05883c4038011000f10894030f15070300007880a800c0c1828080d42200c15001c4031218441440c294810f42c0f01c050080000f071050400145820220642c3e00c002d100c541034610070103c0300f01c444541140200680d020581c0030a0344c031880010012080d0b10150010f0f003440d982c8200c60b49031500d04c6215901308210850030343c040c078110129405501451261a40c0c03001009100724046070043c014500403600c92132480d500000c5030031807654940301203048142c1d85850000c1c1c03140d54822449244c0b0005030801803000e00302d51841c0c02488000119113061040f062010482a21603404803054041c051003003445507001070104210180452010300000742040c14003d64007138102c14880d04503804002c00d103006690b160018030a01104000301001d05100740e504110311070303003002c0280980d000d55807541c40540c1c546040750000c900c04c55030b01c1c42485031603809008040f26840c02c141c41c0d070001e004a6a0541040003c43d015140100304442414140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 355519433 1250 355518183 355518193
    0x140a0507020d0305041503060e010b030c03070e030717030a020f031306081021032a02040b0114030702011e061a0d0b10030b2715010224060a0e0702 65
    0x1035401c2c0a0603146021041c1d0034010284400100300212902c030302506c4005031350000b121070401c21030502c1c151068203c1c481c400380907c208141c02d50b156040741d80188143c202000e0890213039000a103020a0350300404043c0f1460403036241103020010160168601a8003034458003880d600d032240d82d030b0044c400000a03881000804028150040d50340f40d81020700d5a103680d11980d11005110f1140d20901200b03100b81d0501441401071640c003120000000140c0a01c01180f2442c0c80c2c0c1038100c140b50780c04042e1107aa40c400740f0202983c01030b0904d02008075a03500e03c980b41e291940c1d001c0e00030002d0b0f68080400201030000115844135038801c03803080c0c2c1c043d460344040400c0045c00d0b05105401c00c401180240359100504085545c2d00c42c0d0003205003040d694040b4450103110240a200b0420300781400b0603452400c5101880202c0548407580701041d203081403810652003004070702c2c0421510308099010140280d0404500d0680c03100c9200f01e40c141c506c1600316940343d014140100d0103d44080060f004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 355520683 1250 355519433 355519447
    0x304060c170106030e070504050702070303021501030b0c0f0c061f05010203030c0708090a18060f05060c06070305060d06180b0714040b070206041e0608090703150e0f060108030307140a05 82
    0x90b800101c1640f445c000f140c40b420b481e10003240449805035420400341e0303c580c408000305507040050700080e8002000d43c06155265580e540b04004006e004c021500b44081001d003002d10400303040d5000d00d880082203c0c82410024100160403112410045107500c1b10707080408d103035000004989c007803469a81000e181071500c0d15401c100360030192482c1d03031140402c44005a41c40c1c0d4944090000b01c288030000a913280b40020315100502c0580c01240601c04c2403240514200e0081012a4085481c3c200425036a0300c1c1400601100c0c402880201000d00e0032040c42e0039080c2e60940704244600c280c0e403a600945500f141502c0c8840b00d040e4038801500100810b010f000716031000383c0b07070a52006c1c1800341810b40311107907403410280300c00c03c1c0d42c980c0075100001c1006591100d040c642146844000d40318203805c545504000040385204441d00c1d5844107450118000100a07003403c2034840801c0e00d10700e507100d4060b03a440c1e50050f1079402c0024034070042d01002800039800c0f218a0403264481c54500f0354 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 355521933 1250 355520683 355520687
    0x3c0302070f0210140408010501081b010507110a0b070f05060a0504050a0f02061204080315040b1003111201080f0607020102030105010f120906020c030a031808270a09020304060c170106 81
    0x740d00400c070f040050014502220020143c0904080e22449001042d55030510000e50b1602e500c0005a0384425070804a214440e43c001d802c80d444150000000704900801e2408141310ba42e041d4029407040c030001901e18144400c03201c07600740161080003560100d07184c00c034602c000d4a8003604c003c0c1540d004000254000740ca54404801c4c1c40b0b2016044500307054940300e0845a03041e04483c00c0d03501200020070030041043c4205424017091048408001000380180031428807650360001009041e07440461182c0c0600710401e550141844008034412580c440301c1c82c58607007620302800210362191101081001e8010f00035207040c2c807410781d152900d1031b40010088070002031080060055656a420000114200740010030030381091000441d41d036020584001d00710759100442808540c0c00031281000911400220782071501001080990710109141812a802d800481285d0040024400050a120680141d841743e0f02605081200e044162402d90b50f10b0000740c00c54003031020310401804030718 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 355523183 1250 355521933 355521949
    0x110403032109060906050a0e0703030906110705030a0f050706090b160f120305150105030f070e13020301060306090e030c100e0a050708030712140304123c0302070f02 73
    0x381e103001142d440c200d40c07680001c443c01c400082c0e4036282c542e02013040f103840600500c1e074144070f8500100000e91840c0c40003802510117001c2d06007040954152202c4c0050200110000b86c0401000c4c1c880104aa150040400307044c042c08071f403075000e0701c80001407141c02009980c080321100a8004e142c04ca080142003503a110340481102e6410440040c1c0020400382d280400310040e55450025840c00d11500c0021420780f6400d049040050410030021510fa4842030355801c407405040c043c240720303c860300003620444085881c02c280d40c804400000c115a040d080881207860100040190801e00c510480d140e101e0411410704a41c04042c0e01c1c180780035a0f610a501c030616a0041d02c0d0052a1b0f075440d181002c00681c0090700503030000c107104080c043d061040081c6101c071810444042d081c40d110342410350100910260240720b44504801a9a014064601a103c2c0fa00c1c0f450300407d200d900d09601c44008000050700c00d280d440344650940c0c3c068400c0b141800d4101e464514003001c0b6608000c080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 355524433 1250 355523183 355523237
    0xa0b090d0606030b091011090f09100302060a020c040c050c0c0d020105040b04091a0105090307030308060d0c09091104050903071514010e04060e0111120421020c010311040303 77
    0x1580c0e4400c0c00001143c0c00c1131900c0d0040d0050b40c0a010542c2c09803410384265105428840d100710030070030050314039580308020040148001c1c0d44070311203550358171072005507903032607610280d041100050210b1280d40d000c140d040000004882c2003000d080041011030f00d41c02504544965540b1000003420f85140909042d0901ca105240842c5029240d00e06030f01160881d0340b0007003902c0d88903040d8088482040104184a1f1b41c01e00e0943e00f031034902c2c0002942e69441c0c2c4006014805018049211900ca407036240ca0280d030000b080c40f401507502d02110004005460040e0307000050317440b0301841803030180111406014024029410595503440745400a6520754010600b140d5803000a510041c101c0480c1e8020300c03ca0849106629007400c007241640c014146071540c69241820f903201d09407840307050f11b000c42c00d01c40e00c1a4060340c4514200060f035071115140382d15040e058800c0301031183e0000c1c64441c842c400780e03414001e00280703440180d100d01880c0001404182c400b0451043e01d02250012911 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 355525683 1250 355524433 355524443
    0x301060f0e090c0d090219050a0e131401110703110607030501150f1701260a020d0f030e0306090610060e1c03090e270f0d050d0915090309050a0b090d 66
    0x1480031b540011040782c0c00c1c0c10408515014040b0810840c0b42c2034080e4402090340048644181c40c080304400f441c42c016000083c0100da4204003420100d03425440555400e8060665036500c00340b60402504600048812038481d02c141d0b000510038030f2003801014101c0e010715407420390b0b0424440003519144503805001041044801e00d07403056038800d504a90007483c520301f485041d110b101ca9811900703515900d180005a0004045100503141e01603910141030b08500040001c050b1450f0840d1019002c03039000c3c0d0306200703542c184240ca510202d01e050117100c10f220244012a510201580d51119880701d0039401001c0103002403c151400910401440c4a46020345c0c0d01c0b500c0d0340f0009410381068840d00c0016020350f41007003064008a03544602c840c11070b4000c0203286040480180d42c0c0e62040d810304100400031503002c03400145900101451940480f403e0031004903850140300608ac0e414041d4001103140d4000280c60070800050070540b00903049a0385040c1d461803c0c020f00305000001101c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 355526933 1250 355525683 355525691
    0x112120f09170f06042118030201120e030a080f131e060213060e040c032f0904140a050601030504020a06030515060a0c1209050d02040506031c050301060f0e090c0d 72
    0x160a8001e20201d4400c91003031079080380c407486d1040c00101c804a60500349090100409821100e095000c900c041269030901e41940100304c0031003007201802441c4003c0405201c049084d00075a07400c581114866009d05610301c485990700d907203407502c00f514a0f4014280194200c112079030180d0a4a04411441c02038001524240c1c24044102c0700313030929400329000481c410440c58151605002d10071408209282c28000c0c0c1b501f8a2035400203214444400108091f120781484170f420300481035440f1f1541c020300800c450820711803012038003c01203510034401440c0400058007503002e48161401035801900d10140b0381d08000d803c2e4024000039000140100036562030f42c074150340d440018a4485007981d50721141c00c0c03e03407521071401c8000200720000c1c81607891044c820f070b4403503440500840e90100d9000c42e440d01c4940100c0d044c100d50240013040713027440600207070705107401500550403982c55a560307001400040e071003219445c01c007030f541e90b502803a64008504611070007800303804542c80754a0002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 355528183 1250 355526933 355526953
    0x6060d020f310519050d020102011104090c03050108030c1513211206050f04020a1701120b0108030903060a051e010f090c02031617120112120f0917 65
    0xd005604034141c2402c803044105104081d050790a10b12008060940d804003c941d81000180140b50303c03401885c0c0102c080750107180c20b5a2013500120300d0381c541c440f05281e84039114880c010140c001c5a002e5004281480000204820000100d81d0050108001391800107102190204d1500700903240c495052910300080003c181c880900e00c40d461185c89980c4c401094007840036048801c2d60701340908071454007004214075182c400b10090a500100c0c0d0041e40c48200401c292365a403402c00342d070703072514103490700200b27010801c5858000c2903809511540c0003680e850203840c3d0b8a2080994094058000201080312621a03400a0340c00806041d119442240300086090784030000341d0008802c51401c0da0100f2000f030f980d200782e0707002004038409149840515400440c500801403c01030001c0ca1014a40010100450a80f001018100843c4215503075506540c0c0007014440d00540d0b90f8106404d0941005028400c082d03155006078840249180c50b000a01c0d02c07400a081080300a401030060ba4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 355529433 1250 355528183 355528207
    0x715020a0b010b0a0c0818092a031801021c0b0a0803070b13050a1b0f0f0e07031512110a1d060a051002061014150d1104080c010e0906060d020f 63
    0x103400c0011103c11f91504058808040100c50700d070152120300f142041515410b020b030791b991800c0540380c04120b001650303602c03101900d60907440340c0f00c102002544003040780c0e184000c401d010341010b028025401d01492101c0c50070403e0154880c450b6030781c07039402084135a00007000c18400c0d5600501c5040b141c0c01c00d0341c450321800d05000d50340901b00c0e91090121a0841740d04041040b5001401c0b40e5000c41c06c005007040c03181d94001840d03000300c9000080c0d0303100180d00d00d44240c000350200d40c00310040e804da040d51201d540d0310300840340790101c6a00f040000501c240d41020058401140c0c2c050042c0303034126143c102c0707000d03414001034809504010361400c0410191200c8883c000c49407043d034014030162134205640d01140c040c07a0002e01c80700e1550900c0d224250340d0700703a4540c2c0581c0e044010641d43c40780800e1038001400036030141c0c0d5003074501040004112501041e0040401c4083e202d01c2008038542041007081c0204641c03caa020000340400480c40710554041d0401c00b4440c4a083d01d002500e00203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 355530683 1250 355529433 355529437
    0x3170a05071218120c020a09111204051006060c0317060130050c071104020301032103060f0f180603150e031209030c1e1e15090715020a0b010b0a0c08 66
    0x141e10214005924080031420b05001000003000380c03c03800c001c0e000d4054020409840740c801441400d90407440890b00780701d401d00c11405c245515407000c0001650b100c4010c0c08124444074141d020031410200b450841410364a030601c6600165a4505183d040c4170240c440c84810700c1c80e5410340e014049404608510620601d4040d0f48401d0146e9150180d40c0707807507100d91315100c40d0b5070300450041c0010030004241c0300c07200203403000746140051440c1d48440d08400409003503000c3c041045900c030b0001050424850203a05403525985070404205000001205460003072000500064008403420036240321503012001c05200c0400340ca1810b203d440380703410b0031041900d200e0705130b4000182004140c80c041110f0380e10701d580c41900303e43d401c208940f80c40c1c54100c0d8002d032400381040a86918001d04043c800e00030030806e0310b100c085050509000f499074070101401783e00251810100481e0074035000242603030700035900c000201c02aa003480c0c0c1d400100c0e0841041c5106000d4a586100001603903400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 355531933 1250 355530683 355530713
    0x71e03020d14090d0302090306041e05010203040807140a0302060a0e011410320f1302070311190807230a110102060a1b080403051603170a05071218 65
    0x80800090304110883c2070515242159680c180f520422000101da1804900107911540249903600d00ca141140074112110000c00014105d510002c200020014140042d04249000d068241d4074407690402c0c1990395401c0d401d010300560300c80360000e10ba41b00c00f5080462914080000420310a4541a52001525058400407103445110302d0600100842150103c035401c880d04102004000b0000c40d03a1161106010341801a111418000055243c1c0e150144012003040421580c03901c190900504817180c0482c40c101601035840c042903401c0100400c40380040d00300c03401610345812650380240c06080e08a6009060001269003031400c3c20512040e240180580c140503040c0c148807000a083c5280100301c4204c10f407810b021861102c0a500c0700410110060402606603143c50034140c3c2c0d5030241c9141c15000c80422060305c0704165124003040f03903003a10341844410f15112645c40a0036613008a4154001a0444100054005254101300821090b275450b0300c00311001038407100c1c1190b090103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 355533183 1250 355531933 355531961
    0x6050604060b1b160609090515060f0a180306050f0601080105010f110c090108031810050d1e0f060612020f0a0f2c1e150d0b030d0801081005071e03020d 67
    0xb0030410040e00703180149030b88412843c24403000901e16100003451805010030030004c10b02e02040e1073315400d011300b0b02151a08a242d05c100c940d16500c0c500354024010403140c035148010840d020601c0c0d94000d01030f040c1a608141c4413150281c6034a134003103410a107840500d8084d803203410740b0100251191a045400303042c195026542c0d038240900c00300405000c0d0000c0c1400f41140d0790034091034541c0482652222452600c010070414060350f0042c03981d50003421102d400c0ca2030301d2220390b484002ca61080c000c84100f9180c01c2045803e6166602c22070180088004400d8010000040164411a00c000c940162410a55101c00394142280c8106070090000b0300e100b40082e0707028603d03140c445002c2d100c04c001142503d060307400c03074004200340030b07100e00d81408200c5010482080c1ca18240c0c00c5450042c0002d0f040301c1038000003900003009002c0a200c1d9148a00540340d854117001d086000c0c1a10400b05503d40e088000c1c24142070035141d880e0400c0c0c0e003042590030702c0141c111101501554040010721 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 355534433 1250 355533183 355533197
    0x5090c2101080d260106030e01020904060b0a0e0f1507140d020303041103030702030a0b06010e031b04060e130807020103093203180d03021608030706050604060b1b1606 74
    0x410f1001d0801c02416440c0c40c4420300c043c80e40c1000620440d0041d064824520780440d000c02c039080c007240607001d20081141e0060510700007080d1100090060500c041141c5e549261081c4c003a01806031410a07601c030315401000254500502120800c000c280c6603100d19004005050400c0c3e00d030341040c20141102006030000414031062003041c0d000380c2940706084010314509800d60b40084d541c0c0500d6900184481890740c009801130b07020714060780b0001c0002d820b484440010b284284070444114075000c0c403d510b041e07400f144a9075412182e0380325440c0b810384500c401d4055142c0d1040e607004840201c2c1010703182c41541d00013400482c0a112000943ca841e03041c50000c041a03140c0514201410b01c0080d44148264088101c1c1a162504102000d481007a40301d10581012410720120035020606a003504000184100c00040100000c900805081040e03850f40410802613600c81d11650200318000d00c00c913000380c001c41d40c2d440b42144000046540000c0d1001c0c4400405041d41c2c030001c01306d440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 355535683 1250 355534433 355534453
    0x2070c08160306060504110d0911030a0f050f06220804030f05061b0309032203080c0714011701231c11040510180207200f030705090c210108 62
    0x324002d9130060601110103008214002c44c0071038190003010f80009000780c40c4e820440038803002d00c140c0002e0440103005d540070ba6016092009450780002c0086500d0320400c140208004008031b046805000c1c603900d0381454a850300441c01c1400c0c05c8100a9030005400c010000006403460b0010705414885e43c0070700207915102108460b60b840500e03110065030010401c10200300d0001c07003210714008420800019603034011240340e4090b140c0d600010400d44001076205002c1030001140411681ea607044110035100101c01180c070704d05481c95142489240e4001440400b85400a03107205055030340040310300d0902880003c00e000c100410f84400242900503c1c0184145514500504072090b00d090055003080c0701c120381740008a219400040001c52540c01d01e4800d03a8044419107038015101d280d103201032100c010307510800c45040a00c15000c5103401415414041606001c4940003001a80b043d9900c04040a0303d2340445070035500401c110008240401c03c620202d40a41518030003082c40c844 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 355536933 1250 355535683 355535693
    0x16030512010315050f0c0904020f07080a0306032003070b0306040f0c0801081501030807020d03170108070f2c0601050f040b0a031107120e040902030105150406171002070c081603 78
    0xb04c040c207100c00f141d03110740401c1070a0701600d04440e441034080e41c0040c0d4580d40030f150b0070201c0c0200d0308018150a0009040000598150081c10559014800c0751240710b5501140c0c0c94130704c1d49845c0141d0107801940d010060b5180f150003840c4d109c2e0740684086040051440400202d4488003210700118021000500c0008401c00c08414030f56295403410505504548550303010f03014911000303114542114003001014410b0a10503011001504000390039612591843d840b402e10740101804a01040c43c0050020000680314441c0c0e808010a00c0d5403640c21480740010301e000812090610800300001194183c481f0020001003c07044506c644900700840018140c61019030036104282040c414140440c50200c0a43c1c120340d440d0805000460b504c401203800361007031840c00b80d4154a044204a550031400742c4010300050304803810082d0b19281c0c4103601003094001160403490b48401c114040e201810744c000c103056070044030030043c165a1106d03540d1500344440d001400c245a41c1c4d80c04c100b001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 355538183 1250 355536933 355536941
    0xf010c050a1218050d060905011e050406050606160201080907260f0a1205030a060f03030201090501050709060c0312090501050c040f0b040308070209180f0c12011116030512010315 79
    0x40581e00380c0a03000c0740b51400150104000301d001070a082d40e10642c1f5010800254070400f400038140c1c0104003810610b280400003090f0444060369140c1c206000941c980c07034284111100480703102400c180c01c03003d0360011100d215004005090720b200d0391201180d441c800c0c4032070755a2082d410360858002070484c0490350030300950303020054041e40840c0c281d10000c3c045400f0308114a4a915005480c2e0359403819031000340c10507500c0641113446810380401450b6064108102081c0100b00a00c12500c40c200100e8a20000b03105100000e650007a40c074001901c110403052094400c40c0001c600609035445190840d40c0c182e441142100002804014106481800d0402008400c92039401e151854480b404103114040c0002c2c03141081c0c03c00070b440343da5154a60300e101c00b41030085900384e1480701a007e9580c03400c0190684039a00000e8010241001400382005241d0b40030419410020300543c0b02c2d110310f1310800101c0074800148440442000c403d103440740294040c2d12301e81580c1c405081104211 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 355539433 1250 355538183 355538207
    0x1e180a0b010e100507170409060905240f0631150f0e0409051f0c030e011e0207021f050703080a1a01210504110a050a12020f010c050a12 60
    0x28160084403c1c0c0c00c203420005552150f504254610b800c4c2445e1100da0105115035040001080c0c0740c0200400c0c40038903548040c0c403d07180902221546920300e0f421800441195042c503030f100e0700125542c211804d2860207005042c05240703002d80d415261001d0342602010032038000150340361001040000c5441031200d1b00c40c41070b240c18284252202c040b002000303403448190141c0070720f450340030050030070804101040318a8100940c96041038890780075580901a0400040006820524410a00f24040c4510755080d144007225240f0450b22200340360294000b0300d02a0303846084000380442c0180034030304a00451060341d50f2030360b850350340c3d107009428000c019003031038015840c01820b41c210840c00c0a00da2114082420500c00103120f07409004612031180308896492400d050a02c002c11651405100c19034004039601201c2949860900030111540d1180c1074201c04100700303013030240c00c202d0b220380070540c410b16114043c0c0c20180c550b14a8002c9003001280e0544501009001841c2e0002000c510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 355540683 1250 355539433 355539439
    0xe0105090c19060305071b0b0f15030c0d0c0b0304030f0f05070b04110a0807060302030910050403020a0803060f150c010b0411040b2a0d08090c1e180a0b010e 69
    0x10700c220114088206100b501940c81807503507030404104100d024480650240d103505600f81a44086c500c1e2a5903000403e84040e0118404070010810044130548510710103100540140780c030b040c06008211070803603d07001c01c0d10600d1035a100414400a0380c0001c6100d5030003a1604c00380502000c00040050b00210000000c0084c140014000540da03c290980c10940080c550890120054000703070150781c0c41d03409401d452040c010002161f5401d80c020f503105480250554400c80015030085c3d094813022600207005800c20501c510028207898041c40d0083d1004c0e113104404004200801c80c0f83d480341c486100241c07008110b0609146090055244617401601d0a0044200c0c13407001800d18061400382410200c4080351407000c01110302c024a0701e500307201601c82000785019082d01d44803804802401d000034440d000040d03280400044282100c1806040c481400a000004441404144c21100d0340300e060b05003a1550b0780740741031503180143c140074400500c0302d040a0014080381140381403140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 355541933 1250 355540683 355540699
    0xa0203040b01050f120d020705031c14030a02040506070614181e0a0b10080d0306060c02040b060909250c02030c01030921020d090506190f0905040e0105090c 69
    0x820403080d040c11588155041c804210040d0f0000700f005400e68004181741c4034211384541002e50000d0b1000c222031050b03003624a00d840041c0008280c0d05807807028404141118a0f101d00e5442c2c8400459101d40820001400d01e91103c00142d61035124007402c0e1201070311150b00c01b580880441251b50440c0c02c40c10848145507800b05410b4580d840040300494030b9441032081440320030144400200b95a004581454034602070900032019003079805608180e10480b403040c4a028000c0c451101501c031035132120303e0880d0050742040b0181c041c100c0d01a42141c4140041c0c0d51540310181d000340100c03403103480040d113030202d0744001c1c1d25401c0d41b451150400041c3c41c0b03e0340260318041032298000100b03180210344801e680c200b03507012501c454411842e141640c0601910160301140e1075902540359a603c80e2095034800400003540039100c0c00342c00f00c4869040c03045002c0d000302e00e401c19011103800c00603c4180e4800008040301e03105202051981d440c0c81c200f24130040c0901c5000303450803048410311 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 355543183 1250 355541933 355541941
    0x703062705060105011d180403142b02071a1b0405013203090a0506130201050d0e07181b0201020f040306110909090d0809030a05071502090d050a0302060a0203 70
    0x20b907803041c0c10710581c1c0c140300d094001c004000800341c01d03c814a281c090b11440503001ca20010786038107a012201500014440542c1c020000e6000084450f0031060100c0b80219030f40741c080b110100b1440380000341c0056030070070800002401e01d5010620029014148100b0f910380303508420900b84e0203802281b800441044140401e0780c0000203d465201c544130000340090000701d07040440e030000c0b10740000b5402c1c0401049000c0800003002c100c55031040f0141c410546482c10041e031000c409d200001d02045062220480b64102d0350b000305444400e01e0112071380c03c1e0341d035074050360b070005d4035549405440d44035042c11b0459000f00c0b01a84032004544001c600d00440050941d181d802280001070100e0380f2415403440c1d408184080c0c400c10040100b0b200c0280c1030000c2e141d95180410fa00c0750001c5a440d200080d299180070042d2841c0d034440c1e440b41860301d00b05685081b600d0b01c60901484c1200da081c811004136032910460031381d4030f5121324000c204140c92818040d150082c000e0a007801c1d28010070401c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 355544433 1250 355543183 355543193
    0x9100b0409120201150e101a0c1903090b0403080702280b0c16060206071103070b01090e010c0e03100c1103030a06061710150318050304050a0605070f02010f1107030627 74
    0x7c11548100707902039401010209422052058507070408a6225000121407900d924480d0720220512945400c56403550f03e50400313400780120703c8040d0100d981400341d040075003410030400180c1c4480d4080324140407890181c01036101035507008550249400310310813958400800c10030041030300160201103503a00d000c02c02562207000800040400c000d01c4a8055014020070503038040651000070b80320a9a122461a0002c0c100f4001e651419030a03c3c6024203a940a4103080740804400350207407400c0d00c00c030700803800500729540c24401040000c0d683c41d543c0010030300185001e00d0096802048091070104014100c1c4461640b8118244010082c01038191240d241c0101b22040c0d9600c01d0403002c0e052030150010000741d03040c82034050401101c1010010044014410707920100c50640071980c2700d00c030071034040c014010010f00c20750224100001560142c86500d0a6907003078035202040c20300319150942054025802201d0b1241c940c034100610200207010904445a6010b003001810540d81360 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 355545683 1250 355544433 355544461
    0x5090f0c031b15030a021903090f03080c040515070b0115020d20190201111b06030402030703080a110d05030c0d0b010e0a0303050d0b060309100b0409120201150e 71
    0x5860b20200c03100481c2c4405864501400d00016a0192440c1d140d18100103180081c0d440210541c140400905040c0181c6002c1c0c0300c2d8030106600b0201d021001c80c0560b5081e90040c001504010441c4424880042c1550314420b8003c0d0100c459000c403510342400b0f107498a0b0685040c0c10200d01450080d11140b100359000a40c250b20850f07501e4a03028031294500d0480000000c03100c1a1040d000789601d0480c102da0711414009021b100307aa4030302090041c1c0b1182c4d034403109050051000b91010308c401001520b0200e0103160000e000505441c1c00d144c0e60707a0f580186d540034007000401f10300134200e0000704000500100b10b000d807041c1040f500e1441e000301000c2d101c0c8510311004503025034070b41031282d140c0d02c610700f9200c1ca03c6010b40b82e00b051580728103002c1c1c8907800410403201c2031800d00024003000d050000c2941d000b200000c0040c4242c0c1e900c10003541c041c05600d6011038105e5a101c03101c8012035448a2031000d01811500000781c2c0600904404804814030303040320102c0c0021006000b03029880040c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 355546933 1250 355545683 355545703
    0x605060712180905010b090102070803090f190503060711060f01121506030506190e0705060a080703020f041814160309050c03030f09090a09081603050c010f05090f0c03 74
    0x5031030b200a038254512007602c0c010030780103510700d24905070005c240c41d081207004010340c000980032030702c80d13079521200c569892040301e40d081d4000d24040101c84032400c0910844082c000d441a1595072a926800417a151503000c07217140d40003c202c500100344508040c0314040d0040507540c480015581800218044a5484d00c40204048403c0d00c600c2c0e40d514241d0301600141d540700b000d0f1a41e50500482c1c88245008480c40400f01030b00d84440045a03400004c0c0341004c6aa014140d1401d0500104040d04c44610003000032007415009c225000603a4012401080907080328070145412500108090007282d0850710f00c3c881035110b01c0280000c130303205140300c0142502503141c0032518240618241d400c000c903e40145400d4403010545140345400c0e44081e0100078029a500241707541d07031001e000c09640103c1400b130807030101004a110314038185000483d0845c042e0600514145290031f0880c2154000541d03410b40c0ca0b40d60051041410061206a556030b05901c0284029007651340042e417500d01120b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 355548183 1250 355546933 355546937
    0x206040b061306080309040f150302010c0804080709090303111303110a03020316081507093302010606020606060c070e07171003050d08190b0102010b03030412060605060712 76
    0x20002840e542e80d9040c14840b802d4050002e102055030b98104075502c0e04180a150310070383c00d140c1c0340c0000c190356101c0c2c65404100c44040c66005455030f001074940d00400b141c03c1d10450402c03c00490b4000c0200083e40c014a0303903100009600b0300038200281210890700215215081c20007400c022400d5a188200c10340b50411906c540c1340540400049440500303520094041c020842d94440c20351620366486d04540403c01980c0800103500d0041c040b100b81101c1c004007240618100348a280c058807040e00d9417449844c1d484a142e061180c541b148601c400e890307140103039141d40040c010303564140800c1ea04144d054600713904004124141030788424440c01504070207101400042c1c2042d00c03684c16207041080307060184507207040c42c80b104040012540401d95480c800c86140404592040500b24410180c10040040d55400104800c0c080d00b50180c401c0c1c110f40d282d045c10442954240300074001009044c4a1058035805858150180c1c1d6455001920440c001c3c4001e401082c004503100d825580c0318 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 355549433 1250 355548183 355548203
    0x212904021201061806080105010603050115080a110d0504120908030f0f0d060807030c06170a0c020a02060c010c03110903060105060a03060306020d06081516050702060c012a020c01020604 82
    0xa0440742c0186002d5001c008a40c0c0c8245030321801d1845940a801620141c000a0040c1e03a00c0303c0040d000d5510a10541250b1000100a02c5189101354500c0e034104442c69004241001089030300865604283c4c580b00c4465900e1003030004110148003548841c40b20360403e02e031072519203841d807502c034020141c0c0f100b01d091002484c6900e0382507800482d40307006408901080401e40703e0005a40d030ba00c49000813a24444400b5002c51940c2c000d0380305007107000301c80c0ca0120103942d0f5810504003402d103444958040d84524034082d0016904d5102505120406000014860403080700080c11b1750401c01c501500b000040203042c140d528042281030665205403002592070641140840c0209560381c00540b80c00c0c07020a9482e030603030840d080102114184400c440c500074031000078001824054500700201e00186000958503070268005e014000d00042a0a04001d20100b40d6429250740c84651808803102e00e988070740b241075424000305880c84a2000300900010707040045d555013400b4002626074506 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 355550683 1250 355549433 355549459
    0xd080d09060f0504030e03120304020d02060c0a0203060411011d0d030e01110106121104021c050c160f0c0e01080c090a0603080a0c020a05100206190621290402 70
    0x41900700000c403801c2d64608002e2840d060400800c0c85194881852103801020940b2411101c40001e4900850700109580c150500d694200015036208040d8008540514100c4a003da40c0070b011042c070880c0500c91290403c0c454600040c00c84040c8111400c1c42c00c1c10b03444110303491710790340e84a4241e540c2c5420303e8284918258010781d01078010001c50300e529802e00102080a80e00d281074009864815503011205044840402040c0d00482c1881502e55144a1048000e004c590300441c0e002210346e541e0b949060700d00b461041c80d6040c4c0c02000d5a030750540d82c04100c208040c0b40c081c60014500502032001c42e504158615448818800f0210b10680d0b00901085a49100394440c80007554840c5480e9910201c1c03075805080a040982d013a0300c2003947d05800035031403d0020007510244619400341c0030300da907800e1810310b050780c10114201c03800d559a080450700e070b81c00143e85200341d0107114031892035a11502e4111010705801c4070501410f80034070707000803900c171903140c44a4106504450400c10105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 355551933 1250 355550683 355550693
    0xc020c06090a080a0303140f0105010c0b06061b01020408120304080d0c140403060c080105010f02030702010c0f1202150a181410020d02040315090b0106140c010c030b0f0d080d09 78
    0x300035004038503d0302a9894401c00c254040d070041200696011150744156240c0e100d05d526942c00348180ba0118103c0001038000400c01c1441da07500030300c0107091a00702504503540086c4010340705010081a0340c00602880b110604210b085006174000c0320091440c80c107541e46d1030b0f103070088a082020840e1551001c2c482a03005041d0307060300c800e19000083d01ca541d03c1c1030401c084e01c00c460310200401c1c0750000205440d44a00e108003001100381d00110f18080b465401110410030f80071003a14a0203000d440b943c0082c030301032516210004140d0082081400b901d8900088a0b0050a4001c2013464018107400302c42d2150100b003801500700c01e14442101c03488084134102170b641104101c00c64400240d180a9207241d60140013541d001d1000c45d4414008405024129010390001809042c161401006001c1c810401d4001f0356140040b0f10342441302e003001c9182501c3c0e460301d00c100481e03100c5101d000c103030801020030350241c407049480c0c80f02c4c422542c80d240031030311455800c0240541ca841d0a101400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 355553183 1250 355551933 355551949
    0x10091406012a021c121107144204050f01080702010e0114010f0605040e16210902010e180408160f0506040b16050409023612010c020c0609 61
    0x5401070070071004070404210a4031554841c3c1001c990098071540741e250701c14886e0601e0300c00320100c44020081207060981e0059190341c484041640040c064000102141300805c40800088540c0c030301226060900b11144400e41141c04c03058000720f0284400c001c665114075114022170005e09144101d03480d1460204d026000384804203070250301301440328400d8824046428100c55030740c61850203454071403808aa1034400d500c608182c00445d50003242c8804009007884814210b9400d00651903000c81c98425030541000e025405c001b507441106006558002018008a0703004071211081c010140a1584a1460150015240400128000c490310590400100285410400c0103a00244515107180d5640c4d0031181250001050b001213503100d54854080e070342070304070ba031a072506007800d0004010003034020780c100f80e00e01c1440c0c081032801c040d02c00710108070131404492501c1100c40301100b8484000840c0c40003410a81c50a02c03058200c0740c4c0458000b0721204103c94140c1d451005000260400d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 355554433 1250 355553183 355553267
    0x180102030f070b1b21010602010e0a060c020a0506042004182a0906090f091a100b0c03030a1407120b131407020d0926070902031009140601 61
    0x4d0038000840300342c500c80b01c0340d0001e50039141040010300340e83c907580102d00740c402000740c0c000d01e81c0c004404880050b100b41c0080040d49018030403110b64803426112146002415281a80d507104001040700740c0f0b6500d51680f03864990103940500841ca0715031900d032070020102d80045c0440c1e958a0071038001b1069541802d0000d81e00301204280d09072255a5500100109d104d022031580c80d00700c1c240114200c0d80590501c3c81c1d000340780c1c07030f20251516071001d039004030051002e04219051400850340443d01c40c0680310321040341d00115200e09d004a403580441d040c82900040c02d42e0554100518940e000c0350392240d42a42c448003041c02e03101c0b0303004110140e03480303084503042c1401c01590764660110541110305c0741c9010350844a46030400c442c10307038421010780510700c1460b60320034034144407006610718420296880c1c81211030550340d620003d42240c20503202216600000f03101049200c0460143ca603900c2c0311030306d2850003410540e001074441e2511a0200307a60314040022500c200003082c10324008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 355555683 1250 355554433 355554481
    0x90b010c0206040b0a090e0103020a03020121051e13050c060703030f0608160b0906040603090203030d1e060b040803031512010f0b040c050901080a0b0312040b180102030f070b 77
    0x107994813903034104400d400054080c0000742d40b0300030006c2d420500e036034503904032900604064401030554004551280c407114405e081c904112400b5010b8940034846d10788100c1510200302c804003c3c900f00d22051000183c20024500c52030380c4a1404110007060024404008036402940d840310340c036090b000340c400340c40b10104c49840e084000a001350042210382c410340c0489505215183c81c0d0b104501070303020300d802d000d80140e814441445802e001c0e51052144500080450b41800400d446c43c20070741d10b42424075030858014041c50401c20195008540240000d000300b80d0601b07041100060b41e0f80001000030b602e0011121113510706460749071184c54540010b00007401345034082240c01005c0c01a4084850280b4580b85058207203510030003c0e5404000c050703440d44101c0e11810340720703800390034424642a03150240711075180100b0301c060003e00060880468440e01c4512140c400119010541440380c199042000b0808015260b542210159a8407140c80300d181d440f01651040042010000c40c1c075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 355556933 1250 355555683 355555687
    0x11e030b0c0a023703050702030303090c10020c15130305150405070b0403080d05060a090212090705030a0f0b0c0d02040b0c07060905010c0605040203031216020606010e0a090b010c0206 81
    0x841052a10001e0042c0101c1e602295200780890300d808015410032010b4400c0101c0c0c02d44503908a401328401441214060300c0d020f802d0880340e4002030b0440d4019640146564002a0440905e040841035404094000d001904407002d00102041a600c0642c41d802d030320020001d401f56010002349001b902454000040312001096207888410311003050f242924140302d28000011004001812507003030781e6002480d141400c0c40c1c0d1a0310307005400c0184c0000d9000704000c6010a042480d440600303e83d000601d6400c1903030402e4401e05003480d1481d00000d001750800c04506011a00b0420342085584c2d100c0301811480e500c1d02c2000400d030161380c0c012111a0b00000c1d00140d988030103805070060b0031003813060f0f40c08203548038800d80d02025070b8450320b40403520b40b01c60200807072219804190310900140940303140c50a510740d00b00d45031078100c4520729110341c54812201303002c3c0c1c100322030b540c46a000e0900c4003c1b07500740000125034038105e1144038803440d11903015400d1070748249822014035602900c1c940d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 355558183 1250 355556933 355556941
    0xa171f050129120f01060e30120a031508011517010b0312091914010c05010b0907090e09060403080606181002061b21060d08030a050601030f0b09011e030b 68
    0x31305002002c0c414100002c980c050301c02520300c1e0803210312810b00b0322810508051560f200801303950305800d0b80d80403820300450110305503442c0220300812031b103001c2d654001220702c000c0c0c0d0103c024240c02e8104150607032615446070303d0410144400002c0c1c40b4802c80e90400c4071035440159025044111100b60540200184458105401e90240c120140200c4030034208030012250341030303040e000d8032a021001c02c0b50440340c02e840d4040d11002c40e0640c010710011418001e541d0126141c1e0805031005c00010703a1005080062203048031aa54001074000f001d0025400c103078a00130175011014140601c2460300041c0040b03040c208075211107102c41d01410720010100c45280282d2070740000c0b58000030800071810401c401041d02d1084034402c013203a5101c80d1a079940b441c014487c2460041c01990048c000d650000c02007824007000d0751042c0740a060114013072a0172000103003901c1c004031040c51803030b0074603e2001c5103554144c80e4a05554074514246d10035441e80024481240d895030000e032030207600c00140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 355559433 1250 355558183 355558201
    0x3060414012706091e03030f0c020307050a03120e011409010617151e090d030e07050a0e0c131205100501030308150102010b1503061c05030a0e0a171f05012912 70
    0x40d2100c4946040249c681d00d00e00603070b140c5c0706149000f00150080c140040020b8080e4100301d003210005540000c004040c10a60340c2141c1c0c1c184813411a401c6c01804210900b00c09019074406488002d81ca164510140c0001c0e5584083c0c001d1000140011324000400300700b400080822844844254401c0d130f41044040c83d07440d0311140c1c071100002410442e01c5000314000203400001c42d500a4602050145404c0d02d060741e03000080e1000140742c404000100c04802c0b041c1802000d041500c2d01403640e18001d14050b8074005200c5103030340e15107041100410210390012003c0740c0c41190184821040198000102e00400501d240d544d0321241c0070041e00083d08a8101442c411801a1504a0107a03e58001c0201d0304495810080c0164803c100c0c041d00d880c46208078034013818002d030400079001e403070f0710146a610601c5000200181e100140d01c514140002e8001d140d09080404100b04950401c643c00100b0b03400303003c65001403c01d0070f240686a0042c1c100301c030700701c100e2125018010308100d000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 355560683 1250 355559433 355559441
    0xb24100302070c09050717090a021909060609060c02040b040e030328050103170c2d1005060a05040903090915030302120c06040b0c0903060414012706091e0303 70
    0x343d03007900d4003034030100301107000d84a1300d40240d01940302d440000500b12100c1007a10300051880c1180d00581d581500144c03210281340c44900c00a816012001d4103040c40c9804554095022400700308908004101007030700840da0b00c20450301a10b02049070b401c0f00300420084d005000300050544000401c00a1121041200c60705500d8040000130180700880401c0058840a00000e4001404054081c44120118000b00312a0740c01405840040701221609012480503030044850490541c0c09400880ca0501c03400d480146909400c2040b07084c0320380416042c11981c0103050250340d9402c01242850300403003040005203d40c1c001407002600b040e514a00d10f01c41840103c01510a00300c941e09071405150903541102c40820003400199034684031041e00c160007a00a1100d81001c210f035010b00d407018805c041c07180b401001d003015a20b5204103544c1c2110b07520f41c03180340015000d40d01d42c818400150180d50109400c81404280810107083c4008441881c2e00f00501400350304c0000300405d50181c00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 355561933 1250 355560683 355560697
    0x23270f060115030f0b0604051c0605010b09011b030c030305070210050907030b010f060507080304020609210c0609010504090c0212070605091203010302031929160207030b24100302 79
    0x60f0134091401c4140c00c4c0000d41e8903056005a001c00f00344801c2c090340c140b0410b422440b43e00d004001c60a00c1558076820100c603c20f810040ca8030307400041e04e01c0c41b547c00045002c1c0070740c07039040030000d80303041614002c0a44000d51001030070542c6500100b504a07100b006101d079040b0b000380d4200194142503041e40e0307035200c403132104864034500c00e800000c0c0100440c1c2d0300c03000c54441e40c65a520700341480d179880d41642d01c0104100d034000c4050041e0b44c850384034528404442000b400b44084150a0144410314042540200c01e200d08010404140c859a1060590702140c1c0d40f5040403031013181e2010160700301051401e0250400b0800300d88941440490b41105005100e01003c0d0703801c0038084803805100344424003001c3c3d0543d010b031080424107441d04401c1c403c481e010384129505101c2844080780004d07003100c0306403000c1c1a844103115000c607810b0442c2e4400c001500003844040c2c42c40d07842c4a0842001410000d412060803001c0328400d0b52458200080300c0c00402d50300c0709950300c2074098003d4000a0f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 355563183 1250 355561933 355561937
    0x70609090e0303240102190f022e030e0f0d050d0f0501050d0b040c05060408070e0c0702030606010809030c010207060204140406050a05130e0102070623270f060115 72
    0x803181c14070800040200ca0180c40070505505540103d00c508415500c00c0c910228114030070000061114107181c0c8810007518800d1032200303c894243d004001e20f0340d0409000b01442d0190818500340305485044098409645003404104003c5c5a5482810b100212001681074090f00e1a03038800d2503802801441c0e201050501001414001064001128024000c40e500b050745034003c0c0380031408103520168041c0c400c0303040b91141c60702c0d42c02243c2150000d0340103514603440a88284003000d400700e401c6501400142044d414051107800281da1071a024003c42d0602c0040e1020074843d101c2442100c81a065400007035580d4a03540c0b031f001c0c000b580309120701c42ca003105117040c040c92480c1500a031011117000900c420041810035003041801e4900c050749032006940d40c108120f541c00300327001800700d9078021580081d83c106030114420760020490741c00d80100c09003008110700341130743e00a8070241c01043c1807001d190310034030307008a4a01001d034800200284112000048c0060140000a1402d8115 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 355564433 1250 355563183 355563191
    0x20c1006030503090919061401030b010806090115140a080708010602060603060a15180902010f0c0804230910031112071203090506070b010905150907030f0e07060909 73
    0x8424200200d50681c000103001da0420010b103c1146441070110b5048656180101000b07000c1920a100b183d40a500180707080043d040c00f140207603010301c01e000a048003070034070720f0341450704800041c0080414001e03500c072812902da500000c9031243c800c0c00007465580b500c031681c5881100d40a4910130007100e401c0001550700d00085039503440400c44e28041c1001030020045c5490707068040001d040400c5040809040e51000040c445201054022031180910b00010304a0740900004080e010055002010700c044025504002280301c0701304c3d01150b50003084c1010101504d5000e95641c00b00d07001096100300020144010080c003c0b009004480c441c01207821010184000d00481d100c0c1440d48502039000410b08000c002d1103000c2860b13100384a4071380030200070713225800100c4507041000203807005007030180144004103482c42851303040460140c6100b0040200c0c000102c100d50000e0404007010380312400342406c20300642148090408110550b0030311030310759200402c0448c02344540c103059410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 355565683 1250 355564433 355564453
    0x60905090a090803040609111009090b04060b180a0306050a0f05090c0d0308061305010305061909020d020402070f020909010905011401060f080405030705030307050307110106050604060c0c0506070501020c 90
    0x38501c5101c0b091503110980d641940d0342c4e901c03024000e10b000001034078172065011300340080340d40b11041c1200307482507030303c40021240c1800f14204c03c03a40c4540455006600c0c101d41401207036001d009a07114010b0303100180c07180003054404255100c41e5540003d2189040c2001d22160000c6600018542e00c00d1000c00c0040380e0320f200480356901c00200000d50059043e5000601003446100f402c0d9129030007074044023090307058103a41000c072a002da205075855001b490a0180070003114012310f080c514243c00600c0010303017030380015150303c0015000a21880d800940e80040042d060ba07010300090b0020042d144a1034155012030107000c0000c01201d055281c54a4149008800e154882c141c40d44c5503500360102c2542071043d01c00c450040c1003070301c00d48414004070b13001460410043d44200c15650381e40744c403810800c41c0903000a0b060340b0f03608640c1c0d0405a06209680360308040d02d044400300d03d85404040c1840c01c1c00f0702c8070703c401d03001940c012400080c0c250512005400401c42001c02608451213146 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 355566933 1250 355565683 355565701
    0xc02010b030c090115050c1929010e0702010914011a060f090103090f080706140105010c151a130501030b090d0e01140c06130605010b090a1707080706090509 69
    0x2540c0040ca40c4440310400501040c02000c01765110580039080091610a801c03850742d141c0440213032008010030f00b00c1d00c00c004010750042001451102080c001c2840450340310700f80312403201402b13003001031100303580080c160350320075080401400d401000c0da00b0202d13030060440e4082c1001e03038599554031040031a07003410350421804464803110b4002c0380030300708460740c0d0045001c0c00c0d884000303171180c00c07520044002040001c4002c1c100c90340f00c0c0300001040030344040700b43e5159005078400e03410b0110040142c404602d241020304080740500c50b0004d000c1880d40d603481e0720041103003812034004100c1110503007010703a241c2c4941c3c10f80e40111044035503917690307106499841042031009e50018800004402d03255024080c500c03000c400782d00c01a07081c02000c2c20700604c1d0000031100c0c1e401c5446402c49401c1840501d200c1c4501504403058840d180071659004100b440d45640310b009900c070250100501200000d00080d40508480350546d0480741d0b03a00070080007100c0900955106444038008144501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 355568183 1250 355566933 355566943
    0x3040b0708151e010c021f030506010507020108040b071101151701060b221a09011e020a02010513170601031a070e0f040905030f1308070602060f090705060d0c02010b03 74
    0x81008120840106641c02a8500140d14045003418171400380400c4e40181e43d03030380c130020400e240340300206c0441040d014000c041d604d0103044141400020043c160140c1da00990341035029070018905030807a100c81700110b075404014042d400c1d06510703124248905420705001c0a08991240c0e00490846640c4142039080b01c1980c0300f400c00c10399003004600c140c4000418020300d80d10845070203101b0305645580381c003000da40445a5110030303040001c0003003c540c0c01149000042d082801140d01c0400180006580d4440c101d00180c103010021030b210f000f2041c0009154040c081000250740742410248810360f48103c2808202c0d100c1034410b041440d161001c07000f05108009580d910503010001c41c1c10b01520007449807002c1d8000da20381d200c0102080e001c0004000d010081001d4070303507500c107030903041d0b00140c0c860f0001c0c40d10741c006500c00c2264960000b000c64101031076250008854443d06400ca140504983c0966080080480d100e50204119880344801c81e0761034001340083e554078800c05440e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 355569433 1250 355568183 355568221
    0xa02090a0204050909071d091c0c02040c1409010e120a2409030e12100e030d0e0a1208070507052e0509071401090815010f0b1c02130b03040b0708 64
    0x492803240907c04022600245410500300c03400c2d540c000040d19924041c0c0041e0010400c0411944581d160460600f445405000902c1d8030b0510041c0c0d1104118142d148602403c0e1030400c90b0b02c910803d6240c0e00c0304008815114000100c80c0098158074146484034480300809074941c403402d203010700d05a154010180f002e035156648a031120101010400b5400061980d15558881d05903c1c42c0241054803680c40003002c1030307000359164860324000d0419100e202d210b4400b550040d015110008a084481003685034442c1031090269036110b6088941c4e000d40c0d41e000c0c255200c0c82c510b860001001c9204d00d41c40030760500d50780c00e40c1c005030541a01550301c00d861440c181d902c4a6802c100c1041040d0006801e0340c0705140040d00d80c3d60795801329140407400d4000c400c030030b4421401040303002d40c4644580014490500d041c1d040c40050302c2101ca00c18104501c40b801c0136000030703541c1d1100e4905907a0f0030260a0058525403039007010708140341c45200459003100828045000725000480c3c200c4001d080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 355570683 1250 355569433 355569449
    0x120f050403030320070c08070801060311060906190e040c0302040608040f170409050a06060f020a0803040f0c1403011508030403020409060b0a080f0105060906090610020a02090a020405090907 84
    0x40c06186940450003003141e0b614015110240c820710f40801041500100050381c09543c041c0c460f80c0c00c0a00349420810140d10911076a85003920410000b40da80100c2c880780c000c21603006495070702200108100b44602c41405540070a50424108565000708505407409415a001c01c5205040c0e0402d5040748101d01404020808007000940007511030244211264490816455092901000c61641d07800c0b40d00410403c81d04d0320b04101c1c00001500c516070061807180b4242d41d0428a84402a4a4402d21100074020001c0080054103208240d001042265882054105d01503500d402000300050a0340310141b195080c00e1f5000c1c1403150301144001590038000c042d5140c2492b40e800c000040090407021a180358603040c422140e6500c00041200504009001d00001454549164211800100120b100300c80c40000c0c030a0680360100c00300d40c40038090311441040c48259105a140080301e4400039800760080e01008045196034028108441c0300350384007012a220000410b40781e4030140540a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 355571933 1250 355570683 355570687
    0x903070b0c100b180702100203072115061107050d030507021c031e03060510020f0f0f031603030906060b1e0405060909040c0b04090204140f030d0f021e0109120f05 72
    0x13004038800c50711500f0104600450b207165681b080000240d800898000c4082441c01c0c0d50900513403041c0310118070480d40d1403800c2050300d10814400000c418207008400c00c0020303802016103035000070007402010300710040c591800381500d4900140150302c0541b089029105803403404030aa50348218204000398141c5030f85650021420000c041101444110b070201901c906000480b900d0b80e1501302c1000354190b010f0804500c00d035000034502800310340d440c01d1582c4050980c40d00440040151802d00b00312008811141c4400d042c1100030b8022644080d201d60314000000442c1d5400341300600b200c50001030400c0001118284072101d034019032180c180c01800400000702d8a18203da1410f1340244141c00301e85000d81c44000c20300d40740d0032a800802d00d480c0c3c0000c082c07020014001c0c8840c00344200321041c00c45041e02c000484e0712104604640400d00c80c082e00c8a444550003408503170f50b2a4550600f0341ea51402d08020315000c0d204da00010394580c4c4007030418140152244d0106031842da4151100340c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 355573183 1250 355571933 355571959
    0x70f0f151806030203061804051b0901030b0f07120c120605100207030b040503070b010e0603010f181401110c101a060304080903070e09030901170105010c15020903070b0c100b 77
    0x28000c5d500c0144039030f070700ca8159000800d03100c2144000500560280d070041c055a62040681e00b071104c804400c180c0306040d0303640104001141c504040d50300889018480d8403548403500d045d42c02c2c070302020112400c142800ca86005265105205040f107000144046c04591799a10900c000b100e03003210200010703040464280040b48050b410700390080d100d40c3c22245400c3d0161107080c420380d02a00b100c115400c0d04401d105051900340182440032200d580c0030402682402140070f0841c00280740100101d40307100c9078504810080d885101c101c26050415a60365070180c242545401442800c46c1010f0302d0b140c1c8516282402c44010540c0c1400686221700e180c8403074440b05019001941c0c400d90520030520041524808214550f00800d000c10007140c42d03109030780001d406040c005a075010703d640500010495030b03900c42074130700710300303030840752010400c90f642d0040000b9114aa5646416126110000409548030340c010658000c0810540c2c800000380070041040d00c1d03005c0000c583c80700c0c01445c0740c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 355574433 1250 355573183 355573187
    0xc0d3207091401030b0a211502090f0d03030e010c051209010e19110307121a06150706060509011d0f07170a14010e07021923070f0f151806 61
    0x41754216100500b420b0300c40355618a1050040c070382c503150b8004501d8400e480c904100c4414a969458002e09406500b400d4101001c1740000d0103406c0b02c2407162503030202241c20f050281d0300021039106010006e014074004143c02400715801000780741e0b40c5812844c00603c007600c061182c0d110640501010f0240d50422241241843c00d80303c0381500c540c1d0920510304215030342003259034010801c034100d6022050080c03c1403901c0302d030342c0c580140410b1002020842c503641c94103c15070851704262030543d220340703880c1050002030000742c0105030400000d40000c80d0001d0802e82d6043e040b560741c2c91014460341d1349c3d5403d80c2544001e036000000f04400003c500c0d010100f1038000c50780010030342c4000031200104c08a65000e0642a0f0002100b21a4102400701855060008420190042e01a5078001c4201e9645c1c11505004501121280001c903444400d101400d128000c01010704009141c405526121800c42c2c010382803064015205c5050350266010780246440c01c40c0c080300ca0384c40030314280f400c2d0301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 355575539 1106 355574433 355574441
    0x5130e061507020306040611130905091c170421030b0108090c010e100e12160f0503150a0615050304020906180c0d320709140103 57
    0x400ea001d44c03000116903030481e6002e01c0c001003004c1315100c188901d02400c8010320800c03100410019201c8180c0d04424005c81c01841581d0103030f5040380e520101c905d110031111001c04c40c1840e52607400341c0700e002003a502c075004507183e0131030340d1451940340c0c940f400b000c00c3d480202c0d681e0103030a0301c6940d0041605611102c45ca0081c01c90264040020f8a404521040749104030309004425102c14820301c0303048110f10024010301014100859810b40380c1021100c00c2800000a1500144884a5084807400c071a40035000e010b00c00e40e080324110060b840145182c0ea80d9407070f29800509101c403818480300e184040e54503551641802c1c03042003240c2e230002e4200c611419981661129042c03601d0801c9070040e078503c0301c2d01d41c0c50b00e0590b5644064004400340a48038246040503010034514410302c04041c0389401704680c0c0681c0d960b82e06840d590210300031010000704500e05407000394080c2c3d00c = true := by decide +kernel

theorem cover : BRFrame.Cov 355395683 355575539 := by
  have h0 := BRFrame.cov_init 355395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 355395683 ≤ n) (h2 : n < 355575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
