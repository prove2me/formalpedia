-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1455
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:04:03.432323+00:00
-- url     : https://prove2.me/submissions/ecaeec2c-86ba-4c70-b1a3-21a1b02d3e69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 261510791 ≤ n < 261690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 261512041 1250 261510791 261510793
    0xc0c100209040f0c0c0b010f0e0a0b03011e0b0f040905190204270507060207080703060c140409090218070c14030412080418090c0e0403030f0609060801110403020906060705 76
    0xc03c40c00b94908003150b600c9111800081c045c10f0582c410300809450050040c400f90500c04504c43c07502c04044500c21011300422203460700c0c3d56449489030b6094110140c40f141c00c055001000200d00d20800061041291507030181c2c80700c00144200380303040d104000000e038102025140d60b4021101110840c0307548102280d01541d150b01304520f184901b2449036514403480c0070308100700e5490420501c0c000b0254404401c560080e1424840c86201041000441e5440240401d80140048041e04c0040d001e0400004c07030300780481c0009108155801200415000707030381c82c203c2014103c0501c61b141c00100c4410000c10b00e180a21000100c010304030440c820b0303803241500e05094a4940010100d078580b003082d5410746000c5400d0040280c9203031004041590310908003c900380b00e540d4050720078160300c107089032102200f0000f800d1500a80007090f024508034400c000080c2c6698a031030082165001760200c0e50f10740319500007640303118821a415250010f081000d0340d03443e8810020907501019003107400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 261513291 1250 261512041 261512051
    0x708060310020409090c0509070f2a080909070e1e01020106080604030818060907030b06040f060b0a020c010e0a120f2f040203070e010813150b090c0c10020904 70
    0x2800780c0c03000d08043e1510101c0070440c0c03001814601c0844006130445441034800c2000d014406070080340a0040700614182034400c80c0c401c0c1d10445080c51540081050908540ea0800810510400801084008480005103601c801200326140d0041120007504510a5004400c1048007404040d0714030005200101c0c0640c1c0b035803181070806005503030450110710318509228a4103801d17200514080240001000d60707142941005949440e41d110203030000c10760034007040c1c60340c0b034640010441c04000035090214a5441e8440209640300c080400014021140c0c600c800350b100307014583c100c0e40010000e48410f800e040c004101c034820990111243c54038440350394009800d20031403d001c0008040c0700d042500601c1030304050076200c14100c0b071050f44101308000c04031703801921080501c0c5003072038640134598a06102c000c03407015444000d0205408801600e1140703480b9040320601c45810744500d001c6407143c00c0e2582a6008001600d50750303800030f000842d690a101d0f80a000c0c0e806000b800490 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 261514541 1250 261513291 261513313
    0xc022a040f0212010b1c0c0c080c0703051207170c250302010314070c140c0301060801021803011b08100b04080d030524120304090c0c030f0905060307080603 69
    0x8544003850441403840e0040f41409003c035041d0310003801021107951162a003003031101c4070441021101e080418035941e928050354054440c0041c6131449910121480c2d544000c3c2c440f5503525145880112458401c800c3c50082d240240030640d10402d500a481d991101c1c01d0f00c96104d440c1c0c0207600c0340e01e480c0c07065408518150814000e01c0300840351082001619504600004080d61031801c94114000169410300c00b0141d40503ca44440a8002c0a08030401c100f1002550070800b040c1c0c20290b1640c02d141c004500c1c0341042d4000d010407510710201c0c074004007118083c03500303840c0c000761220861a81c080300c502c01103010b82020b071b41c0304481f00007604c00e80d070f15071511a110f9001b58100e2541984103a461040c400d403d88103041d00030300003e6400b1134650300c07020900300120a802c22030340201c200b4004806003100070416500909021340081c000003c80c150018466000041c050300000d400000550250f40100f064809a6601401c40d03803542c3e84961b01a034044401616007505489000c03420b031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 261515791 1250 261514541 261514549
    0x307150e1218010801120f02010c080310091803050703210906020405031006050306070e0315070f1412070311070209100f080c03070e040519110901090c022a 69
    0x6000040804125512242070442c407100d900340b01541e641c148044d820060140da01e902a214080650100020b0100282440104c9001004280081681c040030080c401c000140082d2070f0141d1340c0d2100104003106d0610081031144403204c10150100b80c080001102083c403030f0941c036001ca11821482404415141c1010b400c4903880ca00580309164081414451440c00740b0803107850420b081420300c202d40c00d1800098036a900580403a06101320703c0b00031900b9450500600c0e5007041c0000e0000510b260690011f0407a40c4a2900800010f004407400d0394a00056016240e13011405454622203640d9040150010050520103940c9104240214070050340e507030040c1840b13542456442c450032440d04e5542c05050345a508111041d800c1680c210354942c40c00907018080b0380081da48a0001e80703590418a0519010000703d100a000b001c5800d010300c010300a0b8071241c4441030340d40e0340107a030780d66000d481203401c0400d03030780300507000041040d00202d200b54240f10024442640108034050460000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 261517041 1250 261515791 261515803
    0x1b0503100b0c03040e0105030c0a05100c020a17010c05070b0a0b0109030b101502030405090402060a0e03030d0507020d08011202210d080a150501050a08040501060902030411030f010c020307150e 85
    0x1d000300d078000241801424600e410380c86c0100341c00d03030003031a61020b11000505001041d008103806220001802141244940112846c0f150041d003003190143c0c07142003d5005a2007105415865030030010903030b503c4e910800485e0343c411b8125600111544400e403000740584440b20106042003e01c0c000030001c00c01d210744071400351980f41040c4106500d000034140320381241c3ea96140075900140000c21454584074402d80c1e01c60303812500c081d51084640810348100a001c440c0d81d4040c4004640500c2034420340d8410360051940e0340881e01642130044088480c0903090180700350940180040c5401400c10080c01c0c541031061070750782c070341d9412418000303840e006401c011540050082c405114595029104181c030305031903614460f07419420400041d000d4847d8001e50000c01007103000150502c14203500c054080e24403100f06650b20b04080c00d002900307810a00d4128400d0098000c082042101440740d5030480000e90080e50a0103455280d00903d049440300101d903480e11000020650842070102c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 261518291 1250 261517041 261517057
    0xb090703021305030309010f030213080a1419020a030f0201030b031006050f191203050708070303020318070e0714090423070f1416120503191b0503100b 67
    0x2005890b03000344a804189030505a0160780039401c10000c120590741c1c81110b41d10f120707045083c00360761400d0816204114120540c4080320a0181c0c0649004100b22140d0102c404e600c2041103601241d841c4400e88206201a00001c0d070100f000c2d14200f0001e550303401044070b11401414001105105200400d041080740f030400e40c00141d46920512051504503282c4603456000c0e182c1c040c1483c91b84108030424585401190104988402d1542c1014810380480e00c12561010115880700442d1030080d001c6c2d00b007075030b01c4403914100689001c211400015000200c0388040c0c201410f640340d07a90141c40800d140520261000c004000304001c94a0720700030b80c2c032460074024407408040440300c50b4071314010020b4015400c0180c2c41450401c802d500800340c0740c0403010b011071959561503501c61070b0540d00a4490040050b4105901128450380050246124000040034000c8461041100030112510f01216003221a0b514a05c41c03520780c862005180e001034a42503271441c440c6c07246100100c581000e41c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 261519541 1250 261518291 261518297
    0x915090c17010e060103200d150f030813080109020306010612150803030a0e0f0705090709080607030e0d03090515060409020306010810150506030a11191205090c0a1203030b0907 78
    0x1003407001030b50781481528025881c01a00d40061499561f900f2800e124100e0060079040d2201c00200c401071600c0000c0f030041011008900c1029039070701d86002c2d41e8014180d00781c4201111403000942e69010700400051700d40c0103028003450782c20190b06031101c500d0581100301c8540d90303510148140c0d14500c08000a40700b130307100958880c03800124580607520b4415203840305410030354403207107258000910038042c1da4003120104020340c0c3da260f0444442542c0d6015001d40e00c103400911880c40e401da84502441103400054809811b1444826030640d07030a604010456800152884030000c5200c00d81c0c0d803c911300806c04241c40d110343e00024907028082c1c202072100d4114200c00f0344404003c0c803807003094050481580c11410718000010703600c1d01008206480e915107407504060318000620480d4403030b1281c24500c0000340040c41c0014011298032400c020440d141201180842c00006600000034400170044440d417820504c00c9440102840422000e25031903818110003a0b985910b201c0c42005c3c00d90f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 261520791 1250 261519541 261519569
    0xb10090903080604051503030f0901020312071707020d020309090a0e120319180303050604090b0702070501031409190606030804030f0203100504020114131a0c070915090c1701 77
    0x100300011201d01030042411500d86c096141001d48002c002e59403155103080302c4d146c440d028100143d00b14401e141506181e81069070402c07400542048801c2d020f9920890340390f1907651106020390b6941018103d00740503030700074070444000d85008646503170f00400303103c0045003100e40e001c001d51410303251844017002e654000c0104105800c1800ba1000000140d070380500000007049407808241908050103010075440701700180580d01c840d0040301c0c41c0c2d0b9001403403203034a140c4844000d4492006005190009080c603880c00c111400c84250329001d40040c0d805801c10040b29003209070b00344001401110080d1f254600040401c50920160000f1809043c130003141d00001c2c810942003031407100f441d5a150713190006020150340d00c02201205203050320400c6031b44481c444a80c0481c08503e0344415465031320160b08100200450000d4032001e22004211a40307103807140045010f0721500c0700ba0620566810100b00f21101090300444646441d0307050290061401d0322406800940980019100714142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 261522041 1250 261520791 261520801
    0x3050628030b2a07030c061a09010605041d010f0b030405070812070c061d1201020f030112020f10080c0f0f0d1409010c05090d03170f061503060d0b1009090308 70
    0x81150915000080f402645404010340e4040d29402c5111000342c034081d0b40f0390029005800b80c1100300c03240309000302130510643c1d445800804540c464000c0c807245034400759808a48071880780c1c1c0c070b5058400344100c0341001030500301c5500050700000c005403031502c00d00fa80001e040006000740f0070542e40f407034150390742c0d144d680c03c00307a20100040c0d024904100404180e144410340401000580d41402c54591003010844020180607018020040210003000000081c5c080c40990070084c90502c00d5484c01c00f0390790b00e002000100800e51007101c01090749200021894012035004125000105500d5403c0081000c008412034210201c05420b1903611a41c1c5040e4060320381d18188d01410401c000c0c041080a604000c009001d0304452901800f858104a8209401001042c210703206942c46600c4500e0700130304456113100c1c141d401a005040b401090403c0d450008100c92162401070400e00c4404a0f42d5125588200002d02c000205259907102080100b51401420040c0703000e983e4034042e42c100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 261523291 1250 261522041 261522091
    0x40302010911090c09011d10080103140312070516060501030b04140f030a050705010906050f1b09180405070302100f020c0a030c0e101e1503050628030b 67
    0x3003280050b102e41100070401c03c13008141c208844604000b842d1010003c5041d040c0c2d41e40c940c6400400e25844103030710300051030850303024000c035040360702903501500010920440203403244144e40d0400304a50024001a490030301400040c80203044051400c552007a05480740800c4800c01c0e0001c070792a01c882d5043c8410320844102c2a031903800944041d00c3c40c4050018034590340e101d0001000e05010000c24020300b80708080d070100000e55001f881c14815460404444601d0490880d000b01540361100c40c0c1804914204040d20128000600b00c584102940320440c0d1021030014011183c500c50034a0120068482941c06010310078191260401083c0c00e450290401044024150103062345440c00c0002c00c01001e04101200c4525036151300d59241c0a10b00c11560032150000c0203401d1450703500d01d40129010464100303c45403010300c80e0391201c0d00c0310700f1001d0b0b503400c1e9030080e0b116501141d1500c070308150803a00360340740c1c2002500484c46030340c035610900707482e004903081442444c00c43c0c144c3e101181 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 261524541 1250 261523291 261523313
    0x7120903050607020c031b0307090c051c0e070902090d23100b03070e180102070809100e010c0b07030914010c020708030703091e0b0d0c0f03020f070b0403170403020109 74
    0x4001c4c0060410742c03e40d20040b07503492041d01810403080d00c0d81c001c041c54030b0300c1c20b20100d405041d02c200140000340d108100a03000e980016620302103800e0380044110403038000d2240c04a060f6104c406030a50381e141100c0000a074110f482400d51040c0380c0000000001d10b0b40c0e4403500d5440d400c441004001031000940c505100d40004c0c186052820040900310a82d40441c04100b5642a003200b0340c1203458080030800011102c030700300401303584001800b00c244100304025103d5200c2c00c0310300001072900300208447c1850000d4103140890091150f0b00300145071112116072001c120f01c0d0000c2d980340f00ba251401c454542000c041e10303076503440700c800c400e1650601c500e4000d4500b0303030001c2d807034003542c0e40d07004068187c544181c01c115107603c060082040d104c03011920003440003400b281d03150501900c4017401000216960400308503a4481d58011500038000c0e208040b44040c0e140d802c24009407202080c0c07007401042102040320001000c07245699401103203014078042e0f0f00004d002c2d4a1f9203001402c4071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 261525791 1250 261524541 261524551
    0x60902040e0d020a0b04030e0307030b060406060e060313030e031005060f010c02060f0c1e010203100501081302010e040209040204030803090f0a21090906090c08060a0303020a0314071209030506 85
    0x241141a01c28111a0005183e40205502582c5c01416654500f0101d84c07400d61420080d5040c010150000300741305808801030b008120842e070421000703070760300401c0d82c4580d504024550401c9007070000034031188051018440490003410555400041c5034000380c1040100d4107080001640c680906c80f241c10030880392180c549083c2090a9001843d03000250980542c2c00503840c180c1d070000d1500b118034024001e03145003410780440c410500745904c100c24043d42080310715900d16218090001903940c4201010380c0104141c1e43c2840403240182c004584c40008030f1100c44d009902041195090b0b11984000d0000754041c0740125180e0405298541c01c201001220b80c0d000d900c261944004105007401d050b884650350140c80006070012802a51000055445480300c1403600e9000505d000450300a01c003d211595100c42003559a1030030801100304501015006a00203010200024003e0301c140d807000c0400c503080d80c141817459a035501c60340c1221100b40c00180d01030804100700841006580c4d080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 261527041 1250 261525791 261525793
    0x109050c06090108040f0602041a090102150f0a0213050306010b0a0f030c05030c0901020a0203060406020a0318230a05070b12010608040b0402040f0b040504050c010f0c0c060f110a060902040e 84
    0x854030300b00000344802d8000e040a420b0300810340304030b002c015855044500801403584451001a0220540c078580d810664515000d1f0140780001d86041020028151161200040c1410a52944104a8025084260000c0c0c005441410204503a83c0400186000b40b42c600c1500ea5101090329004240078020b40641c000e060800380c0c940709640d00181074a5214100e8651140c8504240b80100c0c45c0070040b6501130741602801e001d201c14041703280c004240e104a6610244900484043c0c0207042c0803a10001070219103500d151072620100714460901110102c108860240c1c80c2c1d9203809017000719540c44900382c2c1e400054052001140d40a800c0e0050030315041c44002c1e490252101d90070084d0013440248690741c0c40c055809120f84035800703403c3d07150021b00308101610302850301c1a92886d0003c40c05000ca601003501c215040e200b902c200c400150311040040b40c0501c2c1c460250341c108101925a4140400b0b8444d081050b00208030702c0280e140181000b01c0d08408a0062100300c402c0c480c000036003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 261528291 1250 261527041 261527047
    0x30c05030f0f030306040b0a03150f0b10020309090a090c0605130609080a111c060519090c03170418050609070f05161703010e01090f0513320109050c06 67
    0x70b03005020040da50701c040f081d100841e001c248000001c40c180d295401c0240f80703484c423152402c5015041d0b40110480b5101c0d605c01c2040358640001c00940212455032540141d0003004017003814180207800c0c5070442c5030031102060346d610a50360540308005580015001400101d0a00104420504110010002410301029540c01c18980c1501d0309025040604104054004031035180c80e034a44500c0c14504d40340703502074140350500d44800030b00f6069548650b6a8070701412020003110511803190055400005021101c0c81e41e0f03501c90500721b071b00440c40301c405001d0000081134031140e00004941c4040490029680c03a0440c100541c0b020060840002c00c10b0010340e000209800804640c10b400445c01c1c40044803071203140035083e00e0414041c2c11107c0801200016803400d2101d141da0681c2e0761108180b050751602c1a044044510484140a408800307e80b01004140d02c3c0f003800e2160752400440300510248494010401011203000d18020780d520000003082c44018480c0944001c030488055103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 261529541 1250 261528291 261528313
    0x60a1a0c0f0d0810030206030420090106050405040605090142031407020a0c0b0f040305190506130f020f18071d010206100e060102030d06030c0e0903030415020906040906030c05030f 80
    0x350100900040000460f4240ac000150340078070080ca035004028600c1c586582c44202c01803070342d08644201c5000350300f041d101246a2910103040d9060750309600c0d80c0c00381e80c025019510711341c149100c96200180c407039010024440d9040300540025038081d4a0105088100c400d40711841d04004102ca011900400f0001e07001645811070305c8110798070701040075281c0c000c41003240700714866944028030502c82e040003444089018060000f0090154041d0355050fa58840c00519090004c48001c110300300b134484c00d10062501c000b694271703036220180080714496001130000015500640c0c1d0f860125580c0c610740f9241c0c60030601075450700b8900303202410040c03c150354035250101c41405024030900d90b4600143c420b910810680311041c2c603080040c0202656820595001003d5008564004c50381c07200164000c0000070841e40a19413152908100712451404400290095800c0030780c044020040000c56505c00e0184502540c0504080d0b6242c511b04420585402841345090581d500b2a0a840c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 261530791 1250 261529541 261529549
    0x61201020304170c191b15090b180d0f02040f020a0e04050c0c0a11011805030a03031a0d081b0a050604030e0301020d020a020307030f0503060a1a0c0f0d08100302 71
    0x140c454a0751140b1203846075490903619052000c0c24051030029040417400d0b03801d0105d48401d48200c0e000302040441c0392501e965a010003142c442c0841d030302251103000c0c01c0009111001c02050714544480b5040311080e0706c0d1000803004003c203441610b14140072a0340c0401d6142503c681145854240c01c110718044207c2c2002e00007107500e24603540300702d90307840004d44041050b80440c0c0d406001c1d40c058404415403071500103000541c01c58102c0c000b80150200d880f101806540301030585400400912596803280d408801520400010918089007201503040d59241c628911040350b00c1104c0054071000600300d000e691040c03000108801d6030145100fa0045030005c2003030358110360140343c007508142010011a000e88151005106114800200e5206003540031014280071071095079441240034a00a08907490b010a1f51890341c42481c5610030805a0318094600e03084004418080e8103200b02e074400d0070b041078401071038901560010440030700d485510014040d400009410b9490395682140c02203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 261532041 1250 261530791 261530813
    0xc09060a14030102070f0b0a060b03010b0f03070e030d050c0c060403020901181b2703080f0c0f0105040605012c07030e0102090406060908121c020f040b0a0305061201020304 76
    0x10054021000c1c0c108501c5803001e4044891945c0c000716a13503800e0100b071511100305442280e042420314a070220110303543c0c8820040364100c2d1058440360342800d60101c4400d0841c0e002501c02020300840300c1075000a0b0320144002d070320719807442c0c4070140c0f151198402682842d90304c400706880788108110520060350359440c00c9040d40e880000040400b0741c0203040c81c005000d941c10a100b4100101e2011a0055100c40c1c01003030a4100c1c0d448110307281e002050000f6150140c08000d005004c184031800307030f40b50540c002d021a807000c80c2c11100c4044a10a1036401c40d281a5000e44030356450700010701c90751241400341080040c0108813402a65014060ba203542c84000d881102050307150310b10748050240c01d4040d5202ea00b0018000c0250300d45d942c4016000200034400e60009003d4010600040803149061b9218021840541802070b0120032400c8000d40c4000642c1401000502020885a40304000740c40d454907582c500180c0c0e41004400c0194940b2030110001d100c0c0c2c010010400000c28135004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 261533291 1250 261532041 261532049
    0xa030c1b03260a1b110601050f0f0d11150a0906030209010309050316030206060409050a080d140a200405030c010305270a0204061409161209080702030c09060a 70
    0x1944041c08520a02c40148503202c0003002204140306101e00e41616078030142c0490b6210000045542c214142a05c0251a00e092500c0c1c0380c12400c010043c5061680c40b042c1c00302001405101c034010f40c2c800140c032908910a084c1d941d00c0c0041021031550070500961150764030071002d0036042401c114402030450209014113002c06802049803c0e0b140d01982103540c8603a48841a1390f00c5030200d0340541d9080c109004140d0040c819880829080e0034140b0500e42c225030800091f1138603d400351140074a603804076000d07041055a50710494142010300106034043d8030002c0700443d410140440704210105082050000242d04000400c419600043c4911002c942800c0208195407036040f10300c0f403481a080c10062003118020042c01d05003000c03a42070101442100c00b0801152a9081146510030203600c05400140000221340c115180e00a0500e160703120b80380010300303060b0750341035401a6000c200c402c07950108085122070031860244440c2c1b40c020340035145c034000c81c0352080c00101c2c03d258070f1207 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 261534541 1250 261533291 261533297
    0x509030616030612030806041103060a210501050103030f02210904090606030813060908010509030306010c0501091a04030f021b06071e0c03020a06050f0a0f02010b03120a030c1b03 79
    0x140c00c07080380d002c1d800c290001e100702e464100804d403d5050190000c14210b914921852800d003240b00da800c210306c00d69006034005440c0c0302c0c059040c800c40791000107404001c1c01824100c548880c00090090049a028510907550301c070354894040340103451719038241540c02c07515100e8020003404407080c0f01601c01c0c4000495021a80e0001410084024a4907030000340503c8030000740c40c0036404200c00b030715013220070694416100a80e20f14825080309c1042da00304050f81c2081011801542c81060041000d90240300002004045941c07181c40d06802906940300f06503903502007000313158100034142504941350001e4a446d44003d10241e08800280488600ca1325002c940074080c42800c0c0c81c201d4528a0105140c4440c3d081c90401880ca40160b1004034419001d07a1004a0310610940c207450180b2050790089040904914080d02c0100120b4002c4085640c0e139108002d0a560401501451040440a103541c89401c188014244e41450713543e0750034080c4985884003031026a11601140b07507050b02d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 261535791 1250 261534541 261534571
    0x20411031f081b21010905060106020c0301060e0f1015080406050c0309210c060109091110120906021207030c09050d0b06040c051317060a060302010e090c0c15010f0605090306 77
    0x10a0001300320203465a14100c66180c03c89080030804005200c0303058031310341e402311081080d280040500340e420030301886007584803d00100c0e0315250300310829900500c0001c2e0381d40c0070310740700c8040901002c1d0b22b10404001504c440103000c24080140708080e0810240708074146145042110b850380c440c400400300c04007202007041e028455110101f641c90350b03400e280a851366948d40300c00a20140c0000d140944500c01650740d28a090f1500e500840c000c801e60780c84550b54a1036019195004201c4068140d601e41c2d020010030344448510082107124018540b400280c201d1500c0004010784041d4001600403e0341d84440f0011a03022030344154803000444011951041d1944216054000c60908001025101341c01040c4100741210307281030075004004581c07003a070fa4520076805556041c0300190226075507640c110b1039818903c0706182e21420106106241c400018801031904541c405515941040c040050002ea0714250000703004103107526005060003031260010f62079200181c10054980c0c114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 261537041 1250 261535791 261535819
    0x406090626010e10050405060a0903021b150a030903030506031609021c090f030807050405010906030b0d0b0a06080f03120f07090e070f03051f0909020411031f081b 72
    0xd400c0008003100a0003030391a41c0e440c0700851406807401b510700311030720b026000004071492010320401101a0300343d401024010ba01075051001c210380b11403400e070802e19120b141c0c0c00b0840384d2002001080745540c1d000990006078140102150806012113220b50807a42e035813880904544130a10036118a0040140d5a820a01945a030510502000c07a4130a007407101c150280101c0e803940440300c0c2c0c0a43c5030507a0f195181e8100300d500344540e0003081d020036007000040c001d0901c20303440030050742805000384850030b089803074606001100703c410520554a5400912031482d082c00000000318402c4002d5040c842d80845081d0b01c03030401000342620882c1d40300029550ba220307411010040900c00441d140c28240200000c002c0d500c2c03d42daa8020a040802060f800d24800410307442d4400100740d18a41c5a0074100c0440151071012010380e4003903143d110542118507480c0040d4001c0301201c81001324000c8102c984200f030030959010201c16041310100010740e9112103004402c80b00304840001c1c1503004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 261538291 1250 261537041 261537043
    0x90b0103090f030305040227041122020a0f08010f05220501030303020a081317032707050a06020313090903090305030a12052a0d06050d050105060406090626 69
    0x107518001c0c112000304484541415011341c0410b0007140240c580e8141e111642c481c02c401c000240c81540c9181e500300c0009404070741c4c0260f20f42005000100300542001000070074450f525514199441c0c5a42e0000e5000da86640006041100f0b83d801e08112078290326020240c11000a5485400c0c040c862941c1c0c1076012145003002c41c4c0340c54007200010007031940c403410001c001f504209845404a1103601c040341025841a822826241d80020008150540c00300340300302d00e40001e00117110714601c1071001024406900215100c803442403005010343c034501805c12003559a603500c0b080c155081003000c0071705400b000102c0001c5c0d80c12910302085102d0540f404648540680e807024000c1c0c0000304241400a5000c1da00d003100e40d041140a10243d10742c3d20070200c01010741035034a0003a0b030400045504a07010540580903d104841d8001341040d600c1000c80e500b0031142d8000c030b4040e5501e404000d5280b60601c80d00c1c0240c0115542005218100907503041d0034200120492440000f0504078603003100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 261539541 1250 261538291 261538301
    0x7030903020c0603070e060d09020f06030405060411120106081515090109020913020406111c020312100f170105090303060105040608151c0b0105040e210c070303050306030c03070b04090b0103 84
    0x1b034007800d4a50354440c50b030883c9005200c2e121080f4491141d0701d880d207049280c5401501e000f0794000d000350010362166642d1035855116080444d4125228120700340310b4400c00c0c403802005160500c003404d000364604034400480340700108a4078060030060100c0e0074030f0f113424110605547e525280140e071011884001500741c0c01c100000c070340f4540005800300c3c0c02d5078040328100900a610044401c680c3e08106085000840c410f21440168018441054544081407056030030007500c01d0703005001c0781c8030703d54844000310541000e0701c0b1101914512a218209110b055840741d601d202850540c108000000c281744144c1c4074141c1004001c2001c0750309030388003500ca4131228000a001146034281d652900076016500c207403c0e903070801c0b9040006254102070040b10854841301c03001d003440c041000416408421402e556074140c950a21484c05207075010021103001d907001c1e0700c8540d26481c142080500c0d2070341c50710016002c1c0e04210410850101c01c00d044c0d0b4103032001c4800c00704201e01e40c003004070000d00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 261540791 1250 261539541 261539567
    0x190e010c0e1c0602030a1d0703050613150c0807021c0903020d03030b1f020d05091516050a0302010b0901060e010c0303110c241819060b06190807030903020c060307 72
    0x2131000082c4002c0302d41c940d001c07010a040094042d075040c9100301116445500b10712024159030404400200354804c24a00c4448151107030159101c600b240d031114504482907402c0c001e004c0352890041c41103444d010400c244030031050404000c8644690040144600500d01c8000d015104c0c40780d101c420580603400200c101d441c054858021004404903100c4131000384402c0001500441840c68442c03881481200d041c0c0e403001c1d000d02044160141840701d00d60100024118005e1000610800900203010364000c89019034004544d40c400c00f404c00000700b82c10781c4540d050008213101810307141d8001d0f00030380165406003400121240c2d80d203036000309440740b12007540c09030081449100e403000341c03500c2a81c080b080100b42c44040744c0d6001000d4131485811030401010f548044501c1441c030004071000c54201d4800c06021800c03070007a002055090300f280500700801140c5d0700b4a01902a84100019480b2920f441c0034008002d00ba1006900c4070f41c0c540784580107203030000c006045d01d4050200c012000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 261542041 1250 261540791 261540803
    0x80a0f020906040212073203040f02121014010603060509040b090c060a05130803040b040e1f080604031706010e0d170c03031603060311100c0b190e010c0e1c 69
    0x40c941004001e0410441d041d41454001c461045031840d07020362007c0c240c42c0d00d500180146162101c1c2c4038101102102e0385c00f02c0e8015248165491030b54410311190010503031510307002c52055120a40102013090582110042500d000820880b96450700c1c0075035001904034108400a440307840c0c0b22420840d0340310220f40c220b40002047c0c1c11a542c80f070014229144020000c2040585070f4801c80d459128500c180712070f1110510041c0a13101036040c281e504403030061080f50110390f4038549080300d0307011544165034681050041009060308170701d45aa078500311071100b00b01e03803030500c0c00a0f0400e000199240d010303c20b44101c00003040109103000640c03500c19601075440d0050090429900d030b004a5681214210022081d2025070003402010b06483e17000c211200301007001000c1c0004100044821020040c0340111407000c80c1103043c0c0309000f4440c0c50095141a000002e000c000da03440640c000358542e02d80401500d402e42c2c030103070b03d85890b141100c6001001c0f02e0f030780012041c60300010300a002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 261543291 1250 261542041 261542077
    0xc020d02091305010f15052106010b07060506010f1b030c08070602070201090b04030201050301061103132418150c124409070f03110a080a0f0209060402 67
    0x44402c141ca060340040b4400e200a1100c04c00021008043c0d03a030380014804200301e0070b00203101c1c034a031a59081c40041c440044d00c1d151450050071039464040281d0220319030303010009040040c000c0c43c0c0502580442c0c282000f1901c00d560a6004150503001c01c511128070000030b80303410401d0300c9180180005038100510a4607400c03d428418029440311004a0105072015800220a48940d00307542c2200d40507104e17a13007141e00e0305005580750301e0001c0e0b188440e404100000383d80703000c99940c688090a00485055103a96040100340d1000c1c050b20280c2043c40302c460800d150460a180c1498141d80d8100e0258030248858203042c3c5514103003010003071000d181e54200c0c1e519654000502851910b10306a842c54008103101c502d030801d030144500c40c0c0c0e0748451041c0d018002a1161a4503000784041c0f007180c00762039845031801240382140c0c0049401c0c101c00b6502d0305043c074020410801914054025100301390070380d91220101540050001e00400c03a00b00020381959455042d2580702440c00c00e01c02c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 261544541 1250 261543291 261543301
    0x6010e1002100947130209040f110105090a03020d05070b030901050a060603181202030408030a08150103060f0909331a0102070b22120302010c020a0804060c020d0209 73
    0x343d00e0b03042844240480305030004031985480d04c030211061038801040101a0591900207078a00c1410040814158039820090840141c40d280d1402c1c0c07085004000c5004aa501850305c1c4000a280d00c0c6450704004061161070304503641d40c001c0c5800c5940c103c4481001c41c00c2461b21609180f01680328540c1104040200506980c1c1904001d02c510180a004c02115444d80b50039403c860071921104045400503805000003480300b03d40c88021541e0b030040f03908155907060350f81d1455111a001d5000919450141b020070b030010b0302c0c82d07001340030700742414000705041c1075409520707400a204ad0181d25403100ca40209000e469102074440e4480c14400c070b41310f484540341802c4000b041035a1041002d140c10103001c0100e10080380d060300003105a0150001c2403a1064400164010082092410b40c690540f50380342c06510398820000c02140c000410120001c1c00c3c040c1c03c550038580004d0035904030002207070000c2c8504048070146e80c118280080181840c1c000b0428814800c1320003500300e2003100c1449 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 261545791 1250 261544541 261544553
    0x1f0b09090307110d15020a090314070501093309090f0203090c090103240209180106022406131503030302030a0b0312040515210601030c030506010e10021009 69
    0x10210340600c05080020386072030140062880c0040d03010317107561070100c44480b8544441d0020100045203107010110f450b202e44030300114018440b6440b009034071021081001d5600403044030000c02091a81c0c0ca040300c80380c0d0842c0c000810b44222a0f05243c1030782580d06280b4022884d1070302400c0f01000811401d54400380c850001d41c015135000d180303889007540c0032185260684c42103058a60040e608001000e21990742600b280c1c801c480030041940a011003099920303106400c01d1186411204116213500d0076001904080b0840c40704038982120015900301205130030701660304442c0070b072174502d60f116106030840c000b0028100b0304003141c036002e00b00100b40f540c1900603501468084030200300701c140107001c02d0350707500c03030000181c8c01d110062008000918080c1c400840c008124220760340b030b160b803d03040307620400b005001502c4804000e00900040d540d05218500000d83e107030901708481d0500d000042c05002c0305800c014416140028103c0004c0c2c828402030f00c40300c200d10000d0081c4031192503e2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 261547041 1250 261545791 261545797
    0x140301030303050114030c010f0e0d0f080405010f08221a040605090f0c010207151b03050d050c250501020d0c030207150c090b0721020a14010c021f0b090903 69
    0x8074010ba81c01105405d518010424040c02c0205071913900c42c40700e100e14150340c5040d000c43d070703954801d0203808180007003803016000e00306451140203e6956541400c0c0050411401200ca407800c0003591010807040c59003c420325648440001c810488400440c5014444c11072440c0c1c80304c42909200c004d0104206054110303078018110035055800740d0341c0c2582c41980d10740517529642d00591102404214000030b040e0300f140e64070715514003d48252903010000c94603200c010300440006000140400c2d031103280c1c0c81060f40081c0140c644628100d01c02c480001501c05c008000950030303440090510801400358101c0d040061021010310448140c0c40380980290003140b03094400f14030100c540340da000014400da00b02d05450340c88050300141040541041a000000d0482c2d8110010306908095948016107541122580d4001c120107517040c60301d6841e0903000b10051f4a40da040000345c0c03000c00c0d00442c50003481d140030010f404062481d5908400034000042c0f0b0250020f01090905c503d044012000f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 261548291 1250 261547041 261547049
    0x1e02040218030d051e0309070b0c0a05010f0203010302090f06030a0b24040c050412082206030b0409120f05090405040807021503100614070203070b0c12120c09011403010303030501 79
    0x80d600010f00070402610184950540b0101c000150404c05003041c0c020006150040d07081400c94103da9200c5452030740c0f542c4001c21015a9902c001038040c1000000d00034501103032145c05040d800e55145d540812240d81024102c840040c6c8001c00242e4240c4041048002c0c0503041103481000c1e040c543c00281c903042c407400f101c81811013034851014903410135024804568841d540c0f05440c0500d0003516890b03c1c03c0d0301000300d5600c0c004001a11150400d86882c6042c590321400401e03c561501c500034080315002030000d4011400c0001040105038100c41184207002582458545003601c5881140c40384520103041d907021303280c50140002d206c0000003609038244281d0301005000721080e1102482e00080b070306202c400204000500c4500c2c807032003022911068030f9207103c0c00c0202a41c0040c1c00c01002d03402a034400c0e00040307aa01d015a004200d6007100400c002d0a807840c050071200403110002e402071a00c03912480000e00181282d108a0400107100ea10035840750716961a840d0080c0a48000c0c46 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 261549541 1250 261548291 261548293
    0x4805190606080c01110c01080603030f0a05030f160e06030712020310081e0604031b150b0406060f02100b06090a080f1006062106080a03052104030c1e0204021803 71
    0x140c410f80650003061610742122640c030003844800d101c40b00444441c4c000070105034140c00140000422020000040d00101d645500c50799141d01c1e0400f4892420200140810000c8101b1722a03a03581d20380200c1d0201034034400f580c0442e030726961404180d0b090f400c981e11031004ca03440001041184a1040280707404e5070561000d0707410705800780048030007144c0030b00c003d0314142c0c001c50f02284c0000e0003000903e545005c0c1c000c00c00402c0d0065111161011100408001c14640358000f60189240a21410300a00820b09001d0782103064107070000d69030f5038502c004d009460f5940ca44404150b81c0c0d1020384201c28001403180c1556038944004c0c54644520343e41408141c400c00c12600d04000081c051001a45c0840d41d400c490100c8956840c050b41616031000c034141ea0361100085290281480781d00000c034069120b1a0b95008003c590110ba000f000310001d10000c50501030200180c0d01002d15800c294001d61400c00e8100360008048152075400c800a50041c07000a003840400e10f070701a05030344030604038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 261550791 1250 261549541 261549553
    0xe030a09030215040509191401030605040c05040e030405010e03030c0111180409030509091905090313080c0d020d14032703010b0913050a05030a480519060608 70
    0x807100390030f030b40258000c19600c14001000a643c3c4d222024101000101e80326010070400358000040e80c2c0901c2c00c0c3c0041d540035488400b004180840001d0071801420141c50410180074030349002030701c81c05a80550b904129425500c01420f90341001600c9400407048002c011011102c1200d40641e406403403040b03111403640c10b2034115850580b10f60000550545c650301e1a10b00c0ca003080101c2518001d0070100160b0000c090004800c81750702c00d0601c1141081e00444c2d40d42d0400280407403108917540403108540c000d01c020440b6803155040c096040341d0650b110b07802c01d029490207950340858404842801d03c0080742ca80000c000111001003c1e080d1220b082c21610342c084141420f039000c140c2500d0700415001c000c00c4c20408202d444c0300c6501d0040c400c1e601c20300c6043d6552420765004007040d00008100c4401900d425450450911025140328521a029403071030150583c582036003004928059140c914000501138288125180e181e03400f59006100d0445240035801030010f0b01a40802d44168 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 261552041 1250 261550791 261550819
    0xf01020c100807120218040b1305040b19052208040b0c031e090d030e030307061404060c08160c230a0c0b1c0b0103021b010903030c0e09040b0a0e030a090302 69
    0x501c2180c004130f5080c111001c041041b1030522024240c481d1000e50000c0c1c00c44411103c16003280304541c012485502c42d044c0a040400d82c1d1603500900405080c07201307280205204a4021407511384603081c1184034422044015402e0200540c0900d501007007541000061203082080f011006002005026810054068a81e41622158007640e10601d0b000841c03038815001003402141140440c050050482e85001100d0b5130f40c90070340705041240036030203d8076400c3c8410094107005864000310340340b0717015625150801080703422644407010102801200110750b81071041024912a91074101c06100c141d441e20780502c2680d60001103003c3d68010310350312003c500c135640f17481200c4200394480f42004500b492080c3d0301004040790780085051650800050041128810782d8410403a03050000182c000c20508015080d60f03180c005100070000011604500c9581e8030890350740090b001200c4013840da0f02d1429090041800b044a80420301c00403c20014480e4030030b1207041902d00c2610764500c1110b071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 261553291 1250 261552041 261552077
    0xa060309030e0103110d0f02180312070f02060d090b0405060901060f0915030606030c0312170f07030e1f0b06030403020703020603040f0204020d0209032104050f01020c100807 77
    0x15601005000501c00400c214181d13100342c02c0540c4d03000490b5952807a240103918140104c070741c444005000c03940c0128861096468200700322055402c05e80107866000302d00f080c1c403030483c81400d0b401030035007040e09a41030035500d8280507125010005003003081502d10504000318040c8003224101c403644161000142d101c10103006107070444548200014810741000c0c5207401406c607001107041d0160305843c00101150241c000e500080d8007800561401e01e046050130401c0500e40c00558007801b41209020f00320700c401c219041e42c40b0380d1100c01441c16486145044001d016241c0c0c00014511602c072000c04e80501c0c41d46c44060102503c4810820711a40070300f8809240011a406405a007200c0e0040000d8109031006540c018450403407068030035415030020303080307801c44051881c9065000c1424003090400b00010320f1180c031100c0586c1c0070717901c41d1054050b45d4401e50080902445c0819031024041c0d0080050b0002904010311100b0149040c080003032403800110361010000b101d1008421b12692 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 261554541 1250 261553291 261553301
    0x90c0e091507110a061b1e090b09040902031e070801140604020309070803040306060509060405100515091e0406170a061a060705010603150b0a0509040201020f0d020109020a0603 78
    0x6140750003542d80d0441500d074112203070300420090041c401060000390311440b4140e8108001c29402245040601c1c00078504001004428801c80c140026a8007558008214a0440c3c0e41d1030300e01690790381007401003009400384050080d014402c401d01340c02290b03408007030707141d018095004907040d141e1303101006800e80750b1103801c2440110818010072814103080e00256804520b4034101c0304030030b030713655070240ca56441640203484282d0380d02400e006a14000584541043c01110244890305084a0005108105109840c42030b601030860001009254094803090700c0c005205481c48492480c124201800101d1624412442c20201182400c45005848503a80b0840c008004c2505c00e41c5d01d950003400303040c1100700d950b403900e00040a83c2d9610001040c44da80304500200b04140341d07107812041200035000c2c0e0901c0714201a4210242c0d00c0d128009030807104112440c43c203948642c00180e04040e080001d14900340980c6405460081e01500450b59481c401c2d94510b003555560394045049030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 261555791 1250 261554541 261554563
    0x7110d1403040c050d03050310141f0e060a030204170303040308070c05070e01180b040506030a032601120c060e010c02010c0c090e010606020601080a03050724090c0e09 74
    0x1850901020490032200406954420302c60581d2408807611000010009004881c0490004000204010666031100040802407800303402d61202000351030002030f160000c0100021402d407880201030708044c4604c02007010114090042c0303684c0c045001004000e03521500462046c00c811180404041c500001200d108503019070f25841d040c1c407030398422070b07008001030016900c9e44030300300c000314001c00b1081c41203009060081c3c1075950204140c41c942c041e90302c00e0b070300248610b15040c10002c4507207001c1141552194185030555281408d4090310302004c025549400c4c4003c2040000310354440042040c1c030040b0300480c0707040c1042e075581000b11964007601400301d00050900305101c0c01540902c50040d000c622440e1003200003920f520013001125000107207200c0983d11b850741081155010b12005014007200b0300501071001035500d025204d4810010003e0401c0340d0103d00400e0940d02c00e40b07040400100e4242845056500c1c00d14210b4007629000c1e20300e01d007a6441c0410501d00001580382415 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 261557041 1250 261555791 261555797
    0xa0305030f090c030706120f0606020d0f020312040507052d04090f2a0b0712051e0d09020117100e0a1409011a0a080705060912010c0807110d 62
    0x5940751030006a90810161001d0074a11410034034038459581884104081e1242e42c0c0c600710103111000189043d2561070005403803903440c1031401c1c0300c0d580d40880c0194000c012420500e10b06102504228590312582100210b03031710665040c0000c0200c042000b0b0100c0302c084440c441c50092030b03d1500351440a0806598100c03400e50340781201410301c2d40180c0e26080c0201c41c255019107450b2942c0000c2410004220741041700d990325480c942e20310031860b4015012694000341406026a80c00510183c8a60804180800440c0300b41c0000d9144001d91154402d450b68184c03030b5603410b20414090568940c00300c0c089084010300c650a9061041d885200c0d0700396128500c0b1091500066400101010b0b0003512000e44845030607180c40c48142419004400c24000000c4200d00450350b510000b90202c80680b03c0d4002c19405c210403000003c440090343c200300c2d0342554441200c00024541d1500f51110756055007004101c50502b504070088502c01c1e099a140c00c0200104004182d803500042d04521001c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 261558291 1250 261557041 261557047
    0xa05010c0f050409090614131506080a02190b070609030314091e16030f110409020307060f1707051b2109061b07031a060d0206161203060609080a0305 66
    0x8071645c210002c11350250400196030b214068801e4030040d0b04032005900907101c0e144170820031412403450048610114010004a41454042e03903e41941000281c41824500043c440203103c4c0000c0000901c128000659030760010b15054020706600c10f42500800d16203071070880030a12900380d16100381a95409408807a1042c80070301040880c034400120644100b841c500c00c0c0085018a49003c0c500400c3d09010b00a1185014503601000c051000d0045003011072410050b2400100c0000340c6146080c15003000034880350494020810303017030a8a20508040503c000550060001d180700c40e11507030031a890000c103c2450b0b41d00d8042c041d1400003d60020314507200240c08202401c80484024407081c0740103540342200c042a51428007201d4542c00002d4100b040080c0c40802401404080c0c00ca41240c0c81d1540000c5d2544a01300740190146000141c0340e1190207807051a040742d66400704035195030503031800001b00107103114099600403c00d00b20011030441c40c001030380310640741d01d07a84040c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 261559541 1250 261558291 261558299
    0x2070b162604050c030105070e031006062012300c03010b0f0408030a0e0109140a1503020705060403020c0a06050c1009031101110304061109030c060906040806090a05010c0f0504 78
    0x10503003001041a140c0e4044c007003041038290f400707000ba5030160150340e0782e0a54011440b010142003940c245001c618040c1b5100c0c04018980d0001c00c5200e807202090890b4802403058079255007408900314030900c180c0e400145201c08200c04119030081c008511184580d20314031450384403040c140a941c0000003175803c1c001000382c602a680200a00088451003509056441c080c0c0ca00c1c64001400b02c3c0c0c00700b41030148403030046d44d00c080307148003d00381c2d811508121503100003c181803851901400358042039000d403071141140130340c0446682c1d81e4482c003241c2c00361600c1d040080d1100c040ca03c130305105403028440010214412400c0c0c8d07012400b000040c0c400e1850120000c0c0090040441c104e0500c410280701c041110000c1c800e021300c1e2201d46008030340e00e00d4140341020480e4114085040c6820052040318401e840000309404c819000350713590703983c40034042c00007456030007981d0040703035035205140802089841c0480c0c080007252040340281310800d0544000d071101c2c0517a590b00b02c001359090000304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 261560791 1250 261559541 261559607
    0xc0201020c27010306060305010e030a1205040609080d0c081608010905060d020d08030604151401030b150d090b0a02161203090605011202030d0e0307090905010b030102070b16 77
    0x410502c820301c02181288501c280040822400342d000707942e4243c1d10304c42001844000c3c022400510790b8400910314018400c10081d10a44605491401d800d82d0742001038100601d5234003010404c0e42004820382c0303e0440f0503d00024100000700300d00000c0d6040c012034002011141c41007081c030056141c0c101c1c00d030b0803c80715000410005240c1980803080003085030168403a031080d060000d000d18402c607680c1c900784082c00140c80310b201480750220703030b1103004014017203100a40c0e5290050900e00071560185c9a40000c0d0010207040c0700380d520041c00134218082c01c0d200d61154000c7ca10550303c0c801d10303668550002c01240114005d0f80c082d209081d200800203840d00c05104500c003010f05000036000d1480d252001150426042a60650480c030114020f620701003151941d01840d81c548090921512004a9243d910301d04c11440202d440c0d20003c803c21000707400991681001800031501c030001c0381000076003400282d070300d92402441d020410140b684169881d0985510704010b060400f50303003840076 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 261562041 1250 261560791 261560809
    0x709092a0b0912070b0a0f1e0c03110a051204060e060906030c0307031407031a0405010b04150e100c0311060601020303070f020a0605010f1a03012114010c1e0c0201020c 74
    0xc3c0303030b450080d90340c04195100e5180144c00d038025950386540101c25100009001c81c410090600108900e0001403124298840f010804040e0700d45810701c0542050002039141611303800c8003c00c03038002c110050b00c4880b02c0b1000b034401c98060742d6943c03004400e070006115035849550040c5030803000801c0018008844000116000301c424075000921500044e800014003005489400001e504c0c1c0229581c050100c8410014003c011201003002c0e51410894440510492061000c0b0701d078000041d000c16070041024165560002e41100403000c1e035010014482003840100302d02141c40102400100704001420a210f0b07039042c1c005500d1600c55002c10b40c7c14078441341d006000c52240c198540d00241c2a40550340c02400414070345404142421400000700308105200c500400d0309000402000c4843c4030682d00401400140010489050600f6116400300312140c013000c0d070a040c50303200d440c1d80c00076001110746152400304181c0700c4041003c803008885451f0181c0103a0041ca030400c4540fa001c1c40b2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 261563291 1250 261562041 261562069
    0x6020d090c061e09030206120702030d24051c0311071e05010201050117030304030c170a020d1412060d030c050303091f060e1b16050a0210080403140c0709092a0b09 72
    0x45a06201480b100c910907200c070101c9280d02801075441603414403600e07a0307852016140445202d1842ca03c0c62040cfc105100841001a081016039160344140140a0181e00c0150401390a0f020020142c07a0030f0f10246501445428015868140001042c1c3e9904000c0c041c5462203001841ca982c4458030102d40c0682c11401c1650480c034104d103860800d2410000a088001d019009402c4a9030300140141c0140d89642d40780368184000c200042c81b01d80103d00155000070304132010010320b200350034111626880620020018130000090180214000803407403101143d01a401050128100c6800e058030054401c201070b0b08400d80220340d000142c05503c003003000000405904048034645040b21441c09040140c6094000d44c0c013600c15800c041c07040e411140f1050070200c61320709240c0c4e801001c0304008001d94507038400204080b00c00d141c2c00c1c0280001082000001c1c8003550307031402c18078544c500d010840000e01120380503141e00c0e10b07458102c00088034401b40c80113042c0503401041c001050b07051740d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 261564541 1250 261563291 261563293
    0x140102030f0c0105070e0a180f0b09010e010315020f0a030f0b0301020f09090c03011d090f060408040e09010c0806040b03100c0e0306070c020d06020d090c061e09030206120702 77
    0xc840e100303070154940904110b1903041c0003c1414101107202800c3e024400c02028020444030301d06002d60310003600d9a004418603500e0000759280c4803a04000184085240164000e503014000200d50000005c40303070603a0700071074074242c030356614421070000c034032680c108404030001c10b0020340009c038000d9000c400038000100c8085150550030000908a074007102d0301d00c24407000821449403e040004156521898410416180d03504040c0555210b59034001c002e0461442440020032000c0b00303110f80044400a4012242c55090038075000c6045e400c1405104a47c00411001a96003101401840c2840400b52980f4110b92500c0042c44040e214024409405100d0284800251505481103047c5100f556681007223001d11030f403c0500301280500040100030680f049040545d0b00d107004031b95010381c01480140c2d200c00d20a41040a80090200580018020a4000781541d0090007a040241c0405015800081300100a2720004141c1c000650001c1042c00003150720480e0300b110360781004441c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 261565791 1250 261564541 261564547
    0xf0a02041e060803040603060b040b09060a050c060a023415110d06030203070611030a081302040c0f09090e060c0c150112050706050a2102090d0b0414070602030414010203 75
    0x448844150340b5990f01c5007a107513000107402c0008a5052094a01030503640c0112881c144c0360034034583c15805a0000d803846488000b800414050080080720444a41c00040c0d641c14500004004029003001203c1d0350010b5000c0072601c002070582d20010404480d10f070240b0407443c450345981705590742556410360a150b0740c1e50003011144004c0058402c81100b032102040381e50452041c14103044880d0b1114051106201c07281c4106203000c01138600408117864980345540c0d41d00c1006681018006010f5001854074108410080c0d00c00d604201401858860202c00d42d540e600c0304080702c40890030380240d500b044010940302a069401030818400780001c580d1136103c40c01d04130b02c10391020790003c14000701840500d4104070007881050002d080a080040c1007041c4ca4030050084164020307d008554090454041c03c141c203a41a96031540024000040003261031400040026043e2000e0341e040c0340c1d80d15000030404000900e9000e503829680654100ba2038400f045100349800e100700e40c1980814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 261567041 1250 261565791 261565841
    0x120f050c07140a05091b070206070803090c04060f0b12060f04110307022401360f060e01050f0d03112d0c031e0c04050405030403050d020f0a0204 64
    0x2000700c80c002c0d103501078084182c05190030812100400552009000e85201c00c02c0100e554403031820004224407810001da5204400d2000540502c80c005004002c80400310501c40048400100c25820400c140c5080081980b00c4d914400c05460340e115660064204100240b9168180d00c0320035007040d40070701010b00000d851703400607098600006068480d06000700070000283e43c10007585c0b030f0783da050440c41101e0b100c0c0803410b14003491050040125000242c14130340d0301101d01031440003184211402a08105100b14000005070100c0207260800a040090205110f1a08051141240c80040c000c0458003a800207210304c43c540542d081d800d100d1070380c0305d00c0d26412083c00040320b10290030b1401c03a116110402443d01a0824503401f0985500151080d15180c600190900703000038642c0c0700f14189844000c0c1503241c9024401441e0b000b90601040c801000740000c0503000340c900c9242540e401110014040340d50364994100746007194080340f0504054146a84004054100074040a03606403007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 261568291 1250 261567041 261567043
    0x309020f0d030806030d0915053912040e0403080405120a05120f0613020c0102160606050306070819020304030509030d080702010b030703051005060316060201020403020a0b07120f050c 81
    0xe01c001d0340421030320710810115140c18000d50101114500b082d488040c2401003041225070721a4044042c428000342444428500c404138000f000714100400e011640200729120010451800b41c228034402c00c007a071900300d856207007500c3c10750700d04441c946100d50359610708503540ca4014001f985e00340185204d0302c914030320010090540a6490325810354034154100150f403003c500a0181c02100e01c902c0502000c0e989120414641422845c3e000d81ca5410740c41460340248601560519010040312042d010001950085001c440c0210159051a035035a071703080e541e1403421606e55406c01c0110740c10401412495002d1504940a40760946c18451800c01103407605030b99241a1020801403800c00519603424040d08944030300070380c0504046440c42c5e0700e1a0b5100341381020036040f5911000020120345041010000c9913007065a542182c60341c80401078000e5026010680c01000320a2010031000050812030b0405a4002c4074402c41d050310320000c4034094025000d940411208010602c50624 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 261569541 1250 261568291 261568309
    0x50c090c07050f030a08010f030b07080c04080f0a060c020601050d03030c21020309010f06060c02120a050a1b0503010203190e0703061b020c18011719230a0b0105010309020f 76
    0x20010000c60f903401c2c02140c042d0031006d059020071031940d0044d005000103111140c2c42500900a8100403200d5104d14801480f40d010355045071400d4819140c0002180f1000206600b195005030400c01031132032158400c07030302c9130424020140c02008075403828001138401d6220580c402d086103031030140c4100d000c40041640c0c143d456807400d0690040144040400b00b8411007400c0c003079842c0d0410120740380180240c6040b40c0342c14082d04c40c401d80a80304007692014003500e8815030303102c41a43d110b070a441c0f603c0e40200c18030b08100008880e4071100442c69007414401c881c02034000000c401800781801500c5000340588c00c1c100006802035a5002000800d54061421456582600c41001101c9034800a191404860030380307201e00b102c246040d200000d228401410740324060078400c03540d03004a1509140500316961200f24003840314040051054083c1c07415004202106070000003040b0385261a40c80100810280c07a640030b00004115640c082e50101070524806060200301d07545140000709190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 261570791 1250 261569541 261569563
    0xb01022e050a050403030c090609090f060e09030c070f03020609130b130b04150506030f0903041706010e13021e040f18060c11060a09140a03031a0a03050c090c0705 72
    0x26118001d00081541500481f101c00e544c6152800c845072401c100244107007e203201c0c2441084d540e506003034070071440350082030103424030720143e60b16424540c40451340e0f0b42c81180b003000300d8050104041031501c450314841c0102c940082c4840c0c2412240ca04000800c4800145c0300c2c001c640d5100010042d8540c003d110b03045c41e100d0080040c007145080107020035514011400030000e07c080a0901055454070140c076045a0b01800c1103217a0354406a030300340341d03100720b412558941080c03118006c4850000501c16058605070f6a0013030300c50329a816191000140307480029800f0403d040020480540c6507211641036500078004511241c1c01c484100031141461007203041c0f210440842014080309004512680c2c810745043e0401090312000c06884503400303418480e595840703400000a000c0b2034844900c801901038250f80381c00200e454050000c0800c1485d096805029508401440c40c2000d0050b04890f0443c1c041c2c0ba200051034100304104000070b1a424140c0428403214000c12003c0010710180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 261572041 1250 261570791 261570811
    0x30521100e0a151206060f030f0606050409050316020406050607060f0e070303090902031f1d0603010b10031d070e0108010f020a052218020a030509010b01022e05 71
    0x907070400e0324034409000001d142c1540642030084010142c400301c0e44510441e03140050b800061003240c50104007900050740105481165800040203000e5515040280540b040c5001c101107503076181800f056803100900a00b10350802c1c0660f802e45000d041c50b180786030748000c0c00020140e80743c86c00181a0b0b003110000317540e1140c0d00c40528030b80d91407503c40c608800214100034200c0f1451550010810207050140389103d03600440480c04c01c00d1001c1076211500440b504420783c6039198a00082c80d8440f032175800680321040c10104400d810184100b00e500e0002400c20740341802500c405802812030780c0e913100030361040f0b404a83c0c0c40d00014030003000608400301004d681545007991140c00d4801e140b0300c0d903c240e88100801214950064200e8098500038205a400104481c1c01282200303020760050740701402039030301224840300030390041c0b00071440d81d01d0800050722030140c441d0880b021200c8580c0035034041c01055400002406540c6011900300038030071404d002302c145410990b101910641d42c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 261573291 1250 261572041 261572071
    0x40b1e01030b09040809010c0c05040507050702090604051b210c12010e091b01051c0e100504080a030b130c080711061608060f030601080a06060b0406080103030521 72
    0x12640e0305010304440030314110795210050402d500d89548a1007000318660510014803542010400c0080e0184001c00005100708440e141544010706035034840b18040740704880190000742c4519091103824000da040a1030310b01c1083c0620003034105640040c100000c0500700c2954156113443c619521480344405040c85900c0311003000d02c0e09050403040e000700071507541c0001004800c07030000540340d0402c40c00c1036510260300b4440d00180c1d1688503060301041384080203201011060210b42081820594400445817032a18000200f01210006d03200244183c90400041e01c2191103a0803600004100424a58050b030040d03000108454810000071301088044041211031034002004205900e00307100589610f01c0c000486254104544074246d09201d20000401d045484803040c098107000d0180c211901961507c0c0d00962340c14011000300c480b2401c041021031a40307140710a94040741c0e41c0340c0f103508580c0d0840d50103a40070b4102800c6940c5070f80c401c51030104a201c1010f010350090f02150b9150704 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 261574541 1250 261573291 261573349
    0x30606170f03070302030919051002010507021216060c02011e0608100b01050703080405120a110105072604060b0a0e1b1602060c070807170d0206060f0f040b 69
    0x1081c0507040e034404125800921032480840d401108890f2040c008035400070420072440c4030300c952182d041e04110317008079000015401c620340543c4100c3c00359100b81c00301d44000c01c0400940e00d907449000e0303142800040b04006040003620340e030000c0880002c0c2d40000f00310650f000c061090707c40a01500385448989451f410003070000b060100d40d001001040d8280000000040060558454488010308102899000500340003080c080129000601031480b56200200e080007820801010040e011079403030280464142c50140400c4c122064640c030007090120004411030620b0b003002407060f201c041d180d69101c0c440703584000d0b60801512120100502c0c50a12003691265075000190390083c2800420040300010b07900401100308981c1120a00c0e030301c105054081d428954541e20001062090720408118000303421104a0180d050004940e10440305810072071b6101000d83d42103400096400c4d606000341840911030b9100c000150000c02c422164501042c0241183c6030744001010023020460 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 261575791 1250 261574541 261574543
    0x1062706080102031b09030703080c1513120f020307120c030f110709020a0e0301060603140f010e1803091905011d0a0e180106243603060617 62
    0x3038090405500218210720303100d0007440d03818a880d00c0a0340d01e5000850f0200003642e040080d8809158440000c03a200e450b4410350599071071003020f00040302050b80c40001d48000c854081d4880c480d07009100420349403010802038a0f1502d03ca8034030400c500081248070041180300d03143c000101c0d4a80d540c42582c81c070b9810000d01c140c203131401420401894425001e8a0900000c2100c10b403032081c1001070707039050101020303908200344502c8990194200040080c0c4075030190b02c03491024030311400f80b181c607a481d20b502c02c0c20b880b82402031991200142c004038032040004036200c103007828910101c91414800d1000a402101912800e03400e00c0c01d8040103014550748605c8110315000120346c0a201480c045000804078509030007200105015040080c030103102040c084440e254204000700003103074507034400504408805201c0d080b101e043ea0118012640314074060400c00d41900d40034060240440220303503283c0165051040300041004e008404202c480c86600003c1c8075207406031100440f070107062 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 261577041 1250 261575791 261575801
    0x10e0a050c0c150a09020a0b03040210020f03041505120f0601030b030c03150601030b060708071b03020f1522091a0a1e0306091401290103020c010627 66
    0x1204400c040c00b0100c1c42d42c0c0d0000d034060b0b509030341d198000340503a9004d4030000180840a40654001104040096240f120f88000c5014238000e540c80c0c280940402c0d001c2e40d42d0019181e25429941c010131042000d03240c04414152111000d162003850180410200d18420342e094030300700e841800b48410f00c0941e40c1c0510a0703513074015007074000d480320482c1a000680c448040603015414009600005221680b29078425602c0d81c0c001130009480f5186030070182802d400000e0f00310b134800e0003034441c40206032b86405103804495005101403481c1220a091106203140180115405182032042c03d4102d0b80305038007880c0034691051035868140c0341070542000d4800e407c40e580901c8190003044842500d50080c074a0aa90380d18901d1003510001d0b4006080f00d04095101610940c0f0303052410b0104600d0f0b18191558007a914002e00483d03140d040640b22034502c11040c40540070402d05001060350081d0041c01d40c10440c1f000004800340c0c1c0702000c48152400c14541d00d132080c031100c11030220420503c51 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 261578291 1250 261577041 261577051
    0x61b020d080c1209190b0f06090408030103031b0602030901091b0605090114070b04081c060b091207050d030804021e0d0f020d060f05060319110f030a0b010e0a05 71
    0x1090041d81001c800d0803200d80300b54226400d9400500000a45043e010000e1200c416440500d242c006169800c3c00c45215a0950341e00c1052491030b40441c180340707403024015001d0f9800c02d154500d1039103155001e40c1c2030041780c01e05c4820401086589008141141f018611400c405000490030f412180740c070202c104d00c4c0c0e9003074111201056100740300c62503010054500170304003070900d10b150002900c54245680030300200200030081d01000c0008000f442c1004c0c1810240020a01907005910151a0b040d41c5540c05109040d0b54140240c551500d08103100100441099095820094031403020412050442d0000c1d8003240381e1400380000c50500e910245442c02180e15134000c40c000c3c403000640c031b502405801030100340401d0108000d5503107000f900008958005010084805143da0b0000600b400b00c414500c40d00456400c528646065504048940d80c007904021041c1c09507000c02ca00c0d0811100b101d500b505ca201d54040018200c00076082c0070f003409884542a5103480309180080c0d03035000b44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 261579541 1250 261578291 261578297
    0x50a0806040b0601030b03161508070552230604032003120603070b130306020706020903060915100302011b050f160503160e01090207060603061b020d 66
    0x410400807034810150241c010340c0c2480c000c501b46505c1c0000074504240031242c0c080d0f1400070200020f00305402c054803003800c100c6440c0c64106a44011060b0391600448440c2c20301140520101d520107003111044800314603040719000303411070b0840541c4400101148800030580d90785210300d01407100c051090144032440c040306036941104000340d191542800340000b0f00780141c00a500000e01852102262015501c0c02180d480c1d0889100704581040185c881c00d00130301130b401e0702250310300d088400c6614001e0303054100840303146141d40d624000d600826081c0c0b0403a07428890b1907115074060080034001d070614401420307030080c203100201480001418038501003164050400040c0d0f0440084081c400802aa40c6e0b000461810842e042040010b8041e800c0d01488100f0480c145840440c0c0040d148280c0445400c040401054038008001c0e0040c0e545a24091004020100d01034009284140c13007000c012030515600c2e40c0f82800c0c0c5281003501c102035010359030802541c580c10000a40e100c1c251f45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 261580791 1250 261579541 261579553
    0xe01030206041401020a3807140306060c03040e100e0106090501030903020106080d20010c0203031801090f060516080708070c020103060807270204030c170a0212010204050a08 77
    0x40c0c0010304a1003035109080c0303651410000048161700a0015200300c46d0080103120901c41c5400304690041601008504180303803281c0500020b10210344041d1040c0501c0d210800307052130010074241e10703400080003554401d00030000c1c50710500d818809070005002980450b0418142032551515000c0c15810240b0984100341c0100800ca80c040101e0302180c40030700340002c070600c44d800c1c00c9016242e00d81005c1114440d552407081c4075507014020b104520100c1080d0801d1403541f0f400b41307082c1d1300f421200d000140d2041c008500d0700803490412300d00e0180407000001c0c42d00c0c51aa56a407500d18a00015555165039104102d04c0742800441d0900442d024900f2103080d1070440c0002e00326407405082c0c40304100c400f001365811a4000c0d0300c901e014144013801c03944d070151741c2c1030030a101c041102501d2110001e441d012130301e40c105500a480580b640800e0501d2510b0038405402c2e9a20a00044080b0701d106010303c01c1d02589600c14552103055012002681d603900304030502400c2907a5a0040d01198054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 261582041 1250 261580791 261580793
    0x3090f010b01050304020402090f04111b0a1115070b090601031203021201360c020f0a0f0b07050415020f0c031203040f2603090105060114031612061d010e0103 70
    0x4070003205d500a5040b10016118281c040c0400e003031103901ea4100d5000352074007e5011003501030300c024202404641d4048807181c03081c200c09584030f4148a20040c2013780324a8000500d03d02083d0322400c1d80701518400d81000341c0c80d00c0348041410255000d003141d402210052040c404a81d501001c4900c560038103500c2d1480f16426506d10751814440e40716484040c1c202d21903441642c54090b24822a1000d0704410190030b401c02c20014098070306100058852100d5044400300c020a8085c11142c0000c411101c0b0380301a203c2d01c1041200800301020001c0401002c03030343c51490f40041502001a074010900c40c044201c001d0b19028507900454404d030f010f9640072454000401c110b80c0c1c082d81c0035800040d20801440c101443c1d4000040c450360f084152180c0c101d590040202442c8100000802440503489441c015200104c44081507440c03c3e808000052102c03109101000b0400464070380408400603031501e41c03003100d0036030f0401010800201c82e01e162034022065207074054144c4c2c400380801c65140d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 261583291 1250 261582041 261582047
    0x3060608060d03121e020a080109060915140a0504061202010f082811030414060f130303090309031707030311130608091504110103052421011103090f010b01 69
    0x204d038085440c22034a83c003410140c0c542c10300d045060300c1d00114042d520b4003c00103024155850074000c20443e207180010000d0b095205000751348116107070608070200b2905003900341003070258100c07109802610258001030a515544a030000502c0200001c5800d03640301d20006042d0050411080c00300140c44003401700000a0303402420a05d034000300400c0d044103400c03000101600c08608480c5d000c1c030011042100b40004501d031150001c038401e042c0da405940d0714024201045082d41c6c2a0341c11240ca00700ca01c0007074029844560381500a08141864030351303e43ea400111022900d40f031500708004a031000c1050b425004440003e8450702c510390404030007002e19124440310b071142508101d500c80115090510501c8004c0b0200700f201b0101caa14602070030440705140b61518501e0010b4034100000d1151142d4070304c2044c02c1d100110341d044001048404002c3c0385900c40c664000540992088140714040034412408090f03000c0108945901d0000d031428100100e00054440d580d06003d0010070b43da034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 261584541 1250 261583291 261583307
    0x506040c030501230301060306050f1008060702060402010c1b060e0a0806090a1209150504060f1817010f021801090f030f06051305010207050601050405010b070203060103060902030c060a03060608060d03 89
    0x1041000c4c0a1515050100003409441507a001a006030714010a00040354442041c4510840050354111030542c0d42d2000c240d501c0d4412074203c801600b054001c0b1f0b006600c03c0b0b40034042035005038054038000c005008407a02c0315240d6400360011420f0341011819904107440c2e94001080a90040d101a01e0312000e125202c80c00e001d0300804a100410ba034007a400c0c016010310010301105040361340e4150307650308040d010703a1003800340c20007041c2444010a803841c40340003001c00b400044003a010781980703849070b50682c1d8100c1c1c040c450715554881c42c1c101d010080310301c00f60411409080f1807159940842001601c560400d070030082988001c0036081c000300b0301003003008000c664003810003d01c1c1e41e55600c060a181d40c090360010403a50002032401d091200001d1014103a8008503010000340e683d421081700c00d445501c1009425401c1302c0010004a12250310071002e01e070015003601c00e103814440020300345600404494020a0342c42000b8800c06070700c4480c10360f0040c0c0588920b0399902c1c8680b07010701414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 261585791 1250 261584541 261584579
    0xf030b0105150717040501140f070201120b060d0603060e0102072f0a06080a15151b020a1d091912110105091b0f010905060d0209130506040c030501 65
    0x8405840ca042c1c0082d400c21503050b103402021040805011100740e01c0140d00a11806000811040b090050752007004125050000d0600c16240351010907401900d02c619840c6010b24010380e81c1030017038200c0e2180802000418030465001485e14254902203088030281d200c40c40c2c140c0c2c0306000c03840003c0c04400800100c0100b00c441d0f080c10303815000c5e0107803414200010442c0c02036002000041c1640d04040c845000d090007000500c40107040b0300e0421113480c1a442120400e01c0551008130710917019031010711044d0b4180c4964038080003d0380102e0b08031031a0307034450890000203008031000080011a25600302181034060100d070003510a03180da0009007100050b0240e51401220310506000d08031000d1010301405c028002c4e45040030090381c0700d441045034100001b40340901d0242d00d1801011840c4001c00503110301e8100f038104024031844e50803400c504201c19608000041180c0e0700c10560500304c6107180350110f01440c0040134802078a100e103207c10181410140140118499414455000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 261587041 1250 261585791 261585799
    0x1813060f0303110c06040617070228030905030a0c030c0603050c0909070e0306100602070501090f0b0f040305190c090506090f07020a0b0103140c03060108120d0609051f0f030b0105 79
    0x44240050606111076408110303480340000070001f51640d00190a0221110742005103030b050b0391a450f0903602e03103000b64030409103128400258003c0c10780d12803052601c06e0207458035443c0701d9291000707e071911815910a60740c15020490804c00c22203a005042d014001c2c6180a0120342009090b001c000d02440d99882e200351412400154950721070f504c094004c520050031960300d82403044142c1040c0944e4068040180140940450203500820400d0111849448a018010314001c26050582c100280405520b881084000042482001b50f5080170700034904044800440e403401d189803c64035403160f40c01600b07110401c00660380307401902d80d001d01001c81003907042c1e403070304c404a080601e4000d0003403108010381e00210500c07a01d20001e002940c0d002d41210040c1c0c80c400205607442100348140341c0e19a2215101d04550742c588000b81c00f003048030060202d40d858490940ca010360300c1c11100a0581032918020303003030080c43e01c3c070360344024201445990820b60031030f117420003810014010503010f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 261588291 1250 261587041 261587057
    0x90f0601050f010302190903150209090c1b0604060e06010e130f1b03080705010c03020c100b0d0606030305190504050f0411070507170f0105220510021813060f0303 72
    0x42d64020f8040704c41008406040003160480380101900c0001d10f800f040e07980708041001e1440081a03442165212080108105c00fa5542e4000c8020154485448c00340d034080d0b090341c2c0403d20b56042141c0d9008a00c070306404130b100c4e42065005403829805074061003080c082030080c0700307041a80c07410074400180c12001648141087e41440c444280110102c40f9103585c40341c000009001c007142c050040948680028084004c401d80204d00343d0140800c0594250440340c282009904654400c040e1000c002e080c0503103008841c0c481804071903003984160041140055600d82818602203940c80c854080c2c03e0107806c040c280700124400185070307062180100d80c0d4050103134a20b003081d000c1d6201d20b68450b0441c2d160a844568120380328000312007040c403d204190903061002010b0050354070400038503101241c020b41c1810701c0034503609240340a499500509450000110350350000304500328903805440143c0051400303005008801880b00e042084ca01802880b107408290700290460707406251100c3c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 261589541 1250 261588291 261588319
    0x3161401020909040b040b2a1b0d0e030c0607021c030c1205030a14010605030703020a020304030219050108071b0b131a01152c06040f0303020c090c0705060a020c01090b010803030906090f060105 85
    0x8991143c6d1036074040c89d846a181c000c07c0159106210410f15103050f0196641e0b0300b080001d0000c0d81c0543d040003075000c4402c0d8134404044510400e0a65118020324201c3c00800c41921540010011072618400062000040202805450240c81483c1c40380042c141000d604d8540002d11902002d0001010181c000071100e1050b4820004e40d4090368000b0104400449400b18920340c12003540f03e05404200407100085040c0d000d1400007104000414988014101640d2042500f400080c6620800c0c42c0603040760000c111031801c3d17480020401c0002650300c0d418601c0508a40b0500721619003000440e00a1140c0342001010619078046201c94200d0424100000105070b805950005018903081c03810000c2455030024119941c80c0082c1d81c041c00380c1c1c5692200020602c03070a50050220b50011010441c3d090030355008284d02062074000003595006940c42421609085c1d0020446600100504c40242c41c1400b440360045088001414100c1c0700340031981d1950414071501e4850801c900c5885 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 261590791 1250 261589541 261589567
    0xe0c010210050618090706090e09030d090201140309010e0709020a0e121c0201140703020403080307080c0f0a0908060903130b031314100b0303161401020909040b040b2a 74
    0x101c1040034040c100c00c5e207800304609545001900c511300010b1040d040020b06101070b01440341c0214107250155142c1a801c21001024040056040f0704000c040600a400304008401031400341010b40c0c0003255030f040c112091072801e0007030f40150010600c100952051950021400c4004803826200440190210105541444000d10181c0e03010b203e0f01c00d015074410b0f4190f008030b0680d4502d41054046445108084089000d2404010220841040428861405410226804030310012001d01d001000f40c001c03034003900600b08000118042140502000600780325165100790701074000d5003060300b04020300010103030b58824011082c1d000400b2031b800302c0103040c1307a180481c0c00920160014146e1605181d03648290303051041c1e6585002c81c1d402c2645004000c03580c0410556844000ba10302681ba0352840050b0601454003940d0308009502c140c1e26052400740c0b250b8014101d43c3c05501d03080c201115401030041005611070070943c0782e910b1402c150803280044c444480307842070b20750b00700282c13003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261592041 1250 261590791 261590809
    0xb27090f060f04210c080310080d0203120109020304170a02160303090e07171602070504050c13140105160206120405030c010f020306060f072a090e0c0102100506 71
    0x100c015008940401048904402190b402140300d2444003c1c84200c04000c079589000000004002a0019501c000030500900c00780d0f0300301e1290000350707a01c1691242ca251500e100210311601607000440c3c081ca80070040075640e801014a042c013945140792564894004160501210701a41c101141080115108206150325410026000456241c0340d09000e0107144a500c80c82d4480380750070300001c0007180310740f0b90300103401504041c502c020780b642c41c60b440410301c04040b54821445482c00004150703a5038007900d40682d8261521070365451030500c034040d5980403904000340c80070141c0d41c100d64903640801195070b4060903154002880c100d92000400d14406c6000b601c8401c601700c0e090009004005c00101540450f04d4000c11103d0201e0050009900045804681c00f881c1408003881c18003001e801809813a01c1008095418802c0008008042c114034094100350103030810140041c42040c4613110100341c20000a008810301d100000f56244880c0c8000c482c0e00342c58002203006929070341d0503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 261593291 1250 261592041 261592063
    0x9070e060d0305210c09040c030902030c01030b030c06040b09120d0c020918060a0b2d0906150c0106051914010c05160902030f0601080705070f0512070809040b2709 72
    0x403014241050407200b1242e80061005c54803423440c02501568180c041d119120205902801800c03d1156490040d0700a00c400500340743c26004001c2031036000c0d40c48100420152502c00041d40d100c0a480c0240304003819081e000070034903032025509603400340c2c01406e030b8401180c0c1140d0301159691609600c0b80380307405040b0a810584201d100b8800443d03081d4010a071740b034100b59040c0c030b4a174080d0401d00003000340080c0b0788150364054403212043c42c2800840c1d03541c05840500480514200c9190f480c0b800d0b0301181911269943d6160103100501d466103200e54220080c04103100d1482c101542200241c01440040c0d05022050110804120341844081085c14400d15000f080d07950b24294074010358400c950402e078600403040040c800358095100c0c2400b07425540d407180c1c1020000c5d526481c0c05d0407558403d44040c072586a02d07003100400440201211032203082075a40310901c440920080d148501e0903d4030079045140000b4508440003002003000d4441c8900054685400303031418103000955035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 261594541 1250 261593291 261593347
    0x709022215030b0609212b080a11030619030605090102070c050402040609170f1e0d03110a0f030902030703031e1b03030e0c130509070e060d0305 64
    0x11000824400c0d409214140e030926807010301010843c541001110300c91040281c3c0d102c0c00303540400c501401030481d0b04000d41810700455400b00c0561513480c1041036900c016208010061580b21f240581c814620f0b600800181014040740784101103044841c0001041280a4800c00449049810802c48031200a40c0c204004006c80d003400c09505020f948454000d8903503885110b80010141480e10860b0100d50301590f4401035241803d0078090300b61140450814180b0843c03172100d1074000140050924050218050918840c40399605410304e48002900d03014035103000e107060081469841210380580311450482e01d0b040071600c0580c01011600e0700607405104045002c020190003c508800a45400e4000c209203080e03003100715545002c040803202c40a0500180c00c0c002802900501c4058040300e081d00c403404000408121480c01000c0c080300300d1381d202d0040c090b80140c148085006800c1880f00e001c01d500d80310000c5a28a401e030701340181003000025070030b034045084080d45c1029003d410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 261595791 1250 261594541 261594607
    0xa0b060d050106080a0c0e030a080f0d020f04060e09040c1701110d020304110a0f0303080402060706050405060f090a050c0d050f0a050f070905040209150f180417070203070902 77
    0x6200070440384d4100d617000304a900d0805200082070003011107080c0c5680040060001407915601c0d066141c110301381c04940402d00707010705081c05c855030000c0c10413040c62a02407074071503241400040c20980040403550050418106101c0460724242404060b40e00c01c100f040422403100c01c0c0c1d14010521750035007201340080800c0540c0c1c0d200c0b40d600210b000e54041c81403260403030943c8007000540c00c2c50b440b4005044150000c1040000e000e40d14156100e030005042c1c03070820720b032074036140141c0b0b03000c82c2c00700c400341c00000c00c00c500901c0b030115550700454164010524a4500c0d540c4558130110032100b40e204c0c964980c00502007040420485503949c19000030307110342c4003241c5007880d661040300c8403650040c047c045006c6031840307540c4a254415900200424015102d086c14154000c000c500c607150000c482010b0213100340c0380c0b5040c40c0f0900c40c11240143e9103141c24200440301400c1c6034160282103904009000141c0c0c2c0c002400800da680c50000143c2d5211040032045020790b180c980040622111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 261597041 1250 261595791 261595799
    0x1816021c03151e0e0403020c060a0c14300c0d0f020114071b21120e24090705031006080f0105011503020a021e2b02060a0b060d0501 58
    0x540c018480a45007080c200c0074150301d8034060f94070018488802d0140e1089010b080000d0015140e0b800c0d0860b002c1d0055a10414260010500b47e41c0001c40c490042101c0c2c41001c02004044840c3e800c00e1560a009441403000d10301c14289400702c1c900000890004000090380c618500c4000c8135000d03040c543c04c89a01d25a205030280c02448044286c60265103054074940b0036a50180c0e20328418000c40d5104004400714003c01082860199411b4807000d060020714010704004440500243d15161100c040142440d07400384166150364428070481d0b0800300000d010070080440341c00700c50b440030315842c0792582d56029032440e08803140d0045034117210b9120401d0602c40326a00c0300341503e0541040c1d0700b070070031030403821030a9540170320414004c012000004076065200c0e030301030100c2010601c1a03e11905403945a82c036802501543d62046400c1540640c06007026030051312003070305904120710410350750142c010f512030380001d2945007095255629040320340d1303e40701203507130761410034108108dc0c1d40c503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 261598291 1250 261597041 261597047
    0x1e0207060f09050c030d08010f051018081f06080622050601140103050a05040c05040c030e010e1506030d050301090908071b0f1e031106070c15030b1816021c 69
    0x1030380caa4180240104401081051f11412240e41668002030004280625183c203101e000c0e424405032404202500d59944801c120500309000140103410003018415050042600c80c5203440fa6401c2d50b803890510f04111442c0c0104415078030a00f46031400090b1200001c40c00d40410920000030f184e1300a00001189010418200080700d110a80e4100080d50f00e80d4516000c4490560740500101c580031809c10181c90070390005203200c440c514000c00c034112004059420f503501c008252009400c0342403990000844451030a5102c0c034114000c21000010000240c0984418010302da00340f5100c0641c4010300110104a0b100c6590003241541f06c0132081401d8801600c2d540510051007c1e42c0b03400084c01d6003003581d071155041800704a00d030910325542e0707840210580301c1c00c0a40c005006000c0080459404500c400080207096944c00345d040e11554000d04171482c00803410b03caa00304e80f0746e0201d9441c1840354180d00c9030182807010000c8100c06000c0c0c2c0340c01010654038002c2130342020380f04a4168 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 261599541 1250 261598291 261598303
    0xc07080601091401180f1b050c1b0a031e0c0306021803010501050609011d060705070806070302190507060b090a020a02100203040f031805031b0909011e0207060f0905 73
    0x80010b07003001104001103499000020a201d400c60340c0344007010f003003081ca0701c90b40202c4031031910f0503001401114034100711090071030740d00406020400c042841c80c044502484085201c051000d05c1c0c01c990414400010710b0344906000140288840d00d980210b21012103008040b41a00410222a881c1d940c0c6003000c0a9800340e145900d0310004492001814101402954103031900106828140b0345080c00441d08a20842125482030103018070720b0603a510f5203001840c500b0b0141c00605111410100d40bd458240050700700c0b02011310400c0031030790000c102041c4504101d11803401555410342c600f1700c10044e0015031a002c0d0302440040c2400200411580200b100001070f40a03141091f10b440003440403800100c901070028161880d4040000381304016810506e00703901c00c04019107842d2004645081503040c80a042c0d00074100c00d12203113182c5132464980c131011103c003e01108040803248400c908084100940f144e802003010010000b50360070803580035005520811100e00c26041c42039440e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 261600791 1250 261599541 261599549
    0x6010e070c1b0902041d19020c0c180402030f0c03060106030207060219030e070b160f02010210020703090906210303021b01020c0a06050105090112021c140f10090b0a020a050c07080601 81
    0x1d600019065410580207000c240b145012060787e030304c44401c0c1d0400720041d52000e44001c14900803003022005a6442c1c25a400d10705007900ca00c0d100e249030a2041c5841c0a210030801d103892760026940c1106650300040302815211607180158882c1d005180801c042d0007808060805000c0c03000002c2d100e180e25500c68600c0c90000c0b41244c1180b80c0d00c1d002103030382d8030542942c484561134800015010404202c00baa1000b031045c41120b4034400003030301607412604a158110f000855401d0f04200d51580b03030045c100070741380024420500202640429200e5907410400506058020820b4611660860b11581d41800140001d55488006c0d102590715005841000c40d07086250400120305410404c40b828162860b0301040c901d040d0082e002c01141e581d003420850b40100340c044c44240061403a481ca080c0c041940300080c0000340703085291070f0404500b42c00e03a0350401e1070a001c0d1004540c80d540c80c0d90b00041494001030350f070310003c982240c45200c2d6150411003440703a034030009404c5c500018124125 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 261602041 1250 261600791 261600809
    0x8030601050a2a02010f030605130b060f0409151710051506070b04060e0304050d080d091515050405061c0c0f06020607110c0f100905040507110f06010e070c1b090204 73
    0x1b0501040b0950407205207009164024016a8106181c81c0740f580c06400b10010040105080c0400b00105600d0b95105d504200c1c209a102c08200005c001918000805031807071106440003108001c00c0207640d43c01254078854455100c802241c14450803c00c5016840e81c0904281d41c0d031603040c24034248200096804480700c40c68800e10b000d014801100740c50549000900b000100442601d074a142038001007403080100343d0354010680054034502e1095851221140013007074041d024a030228003030325954001406641401c040042c03507911020210310304544242044015641400c2c0940d0000c059000070029021944011078510340028049225041554840a06803108600d184d1201410005550801c000c40b00300c203001c0ca40b040200c12822503501c0c120748496941d6000600340c030816160900803606c4840805501081401150902007440f40200b0a9503d0300480c04031501c0c3c002d200004000349808480100519482007076010282a5030301070710a0b49502d8000c0007135005200340411 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 261603291 1250 261602041 261602057
    0x10e0d060c2d080103170903060106030c0206090a150e1905010203061005070b0f06040f060306050118050402030a02010c03050d02070c0e0a2a0c0b041505010b040308030601050a2a0201 81
    0x6810054502c1030000c0e00329944481a5034030716034490180350020381a9404100c0d09104810303090300d0802400d0b00a1242e0b98020901d0303410308001904250002c0e040c1c1c991038004e440410301140109026424480a0a1000920a002c01c00d214203001000380c04014100795176810b802800015000755015030411244c40343ea00d461540700362040e03c9a058001c14070a02c80380000c080000c0d82c24445d522003070203440822084070114140c400c40d001c64100b2030f013103540d61005211880340a0070109903c02c488108004506068000070741e5444071603802410400d02e004c6d400308051144060381c519225104056445100340c2c5400c0002240c2806402c12076600100051080d4501340180c41c075052070301702400f02c1c0d141d50044403900c0c03419003a0064107000b08081408009038021560703912a901655445150140c0320402000391241a03002e030566010500c42030001c80d1500088039009030302400c150b6941c1c50107a500741d80c030303103e6580c4140c11040c1c903002510b000d90880648031920351017685c030540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 261604541 1250 261603291 261603347
    0xd06030212060108100b0d05190501110a0c0602130509090a120318020d141002030901050a0c0906031e0903020a06050c0a020c090604021306020d030b04020414010e0d060c 75
    0x1903181d90901c10484070b0381c4517803601c1d84e40403125400700c615003001078201e12490546454940c5884d5490f107682c00301c480d003d070615092020a1103240d103003c0402e69403078540f088070500201040700c1788001a000507800101200390104940c3d100b0000c100141c2641c0039403030615070740c03a12940d4218050700d41003683c0c2040380c00684280b04400e40e50442500440c811b02f0503400b401076040250720122071003100f0800700c6035031240802c5030103020b031101c6002517030306e1514201090a66134083d05100301c040c20403d0790010301d0340291480c02600c42d01e1400044015030100d607981b009502d6030766400c04c64a483c690b8420302d50301240c11846030f0b004210520060b2a080e8481040c0e10074919902d0051f041821040381c00c0c07400103899500007000901c091305281c100c80f00200320541552004001d03a00c482286200103030180100c62488034221003c50074203280605911484d40008040c0d41001040800d1002c95520405180203d0750002010030501c101840003415950600c03a41070800c0c010400003175 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 261605791 1250 261604541 261604543
    0x1e0c11010f0b06030f0a09020405090d17040b2413020a020d0e0307060c080f130305070806011401050304261b06010f12140114010320010e01140f0d06030212 69
    0x400c1c0b2801034003840c510b9884200005990401800d0014843d4492a81401613507840c0161801200303900041c0071000081d1b840038241c00c0401c3c5c64034040100c1c500801011682c0742116035400b207450758584070702d03592850f8a401c01c9030148031b109501c00d036030b02000c2c0c20b198104d074090180d003107260b02203800d80004c069056410401d9024900c0e8941d10407401404964801c3d0074031040c0511620880d4240100742014042d0f50700980001010300d42c3c0b8440400620070100301107030040c042007018200035410100c0c24a100c030890303440749044c0607000000c47c2c00c119152507494041810207001800b008440403d10895038410a1000414010140c101c4800000820002e040301c4003184010f9011345050441521004614800d0710070b000c2d018518580804207005400443c00115890034045d81145803010f450420300d060240f20150b24480942c569801080501104500b401d062480d03140685440056100d03220020320030b8400860544044202d0760004025240700300c0b000102e04182803061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 261607041 1250 261605791 261605801
    0x1e0b10080604170a090f0801050f06060c030301030618061b110102040609050418080c030307031b0e1201020c0106060c02030c010c1a040501020f031e07030614041e0c11010f 76
    0x343c1083d43e40d510440c442820407005007500503440c00c1c00c5448650343c1c0001200f001140e485500c10341d440e03400704072850041c43c0361386601c03c1040311180e05200055640303d560780014000141295941e803199841020702c0210103034000d03403040003407180c408181c0842111011a200210101e4030a4809801094060081c1c3d81510180e5407207111580c5440c1c00c20000d400501020b03451200b172403811101040e078a00003400c0c00841c45000319600d06001000070200d4004001100c00051354000c0c43c102c180e40a540001422400c5950681ea88558040740d0b00a21480009404540c40e052001883c0b40d080680604064001ca0544800009010044d5146421144018104401001c1c003202d61088600c40d540c100c0c2c0a48001801c1011100f0100c240b980141c4849a42e04004450038443c11569a86142e1090036031406011440c0740100c1546201c0d00030030064401e03170300d0780c1580c400e034152100f00d940c22150610040c0601416290003402070044041c8602c1c1e65400d20340c411883d00c00500034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 261608291 1250 261607041 261607043
    0x1090506092a04020d020a0c050d0306050a060503060102010e1c140c030a0f14030f04060e0f1b030f0a0320030405030a061a03011104051002061902071e0b10080604 72
    0x80c03007030354004000384660304614000b41d09034403580c00d020501c509241ca1000e40303400a11604c80b09503061480c10043c1c0740000c46407241003018103290041c00141c071411316400071140d803801e2840d04c940361980141e026110650b4900800e205000708030500381c140c1980e200741c108440e105c4410084040420303020360322a4010385091980300f00000c43c0150f2141c009141019402c0c98124403c016295200c05680d01c00d55040715900d2840d81480240200380c850034402d4031036040244207030a030300000030740c5a0455074481a160f41c948881198a610280800841c1c0040c1c2c506070707213443c0198034015007000d1400119003c9aa9404200d60002400104035015203000030028000c21000c0e0383ca5a001c3c114080400b030001309520810b2105031001d0041e0b90003880f410680e603480f18140828000040020403818045500200074407089820200a90480030041c5101582d103640e1402c08000000c000110031068507215080c460510101c070710294080d11085120990080c0d45070917040d0342c0d5806440c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 261609541 1250 261608291 261608323
    0xa17030105040c0c0203031e1201060203030612031603080601030e030301091b110616050d0e010501050f0a03030503180304050901230d03051207031509091109010308031f0b0c0109050609 82
    0xc408c1e40e68110390103020a840f0901058a0316011200701e01040c0c102c070aa00c060301680c400302c18040140317840e8421841040402c0011070900346481c0b98501480715020016007800440c3c0046603a6074880c3c0c00c550421141d000407250359580d19031084008100394060301d01d0880c40848610340c0c0e28443e070341042c03c014a2030020301a40e180c41c0e40806000c00451500307000e0250402aa04144025004004504407c0800040d5541c50001840010080d00034107500c20a40028240002a040016282c0080c5829050a103517022820407600d1449540c00080d844841e0030000501d101c120740001c09400e108050501e104242101070000078000c0400c000d0205000f8010a118035030301007890756014225180105510800407100c41c10300720207400140f146a1211303504820711580320713030043c9412000d4603400e04643c555100c0195601020748403024140001410b03028082103510000003601503109503c1e590000d0070b1060340204000101204d99008180001d6107898001c00c0c4880c2d40c2c80c40d44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 261610791 1250 261609541 261609547
    0x60c0209070302090607151e05010f12060609140a0e0307030f0e0f090c07060e2d0703080d02040302030f0708300c07030506090606010e120a17030105040c0c020303 72
    0x1501a406504103204854008000380081c10100c6c22201f4070300d82d06900f99900003010320551041040110111040c1c03070f07203103080400400000150000e400111000c1b1400c1145042d9140392520242c08a0b42c44020540c3c1420f00c80d00d0b0744071100204901414440004020342d0750b41c180c0c2c03180c503405800f0025003c203075410711401e046c0b40940061904c4c154010081044142c4802c006a001703c1c00f550342d40240300000c2091410403031148030700088101068010101c518800c035400c062144040310418140d03a00310210034912104204410141d81d104c115503843c1c241000c0e219000303411521060f0301c04c0c032610790030082d010b1021907181c040d03420200191442503841d503011640c480c8240701c41c00c80713882c0c92000a802e0fa08000e000d025040800c101600d00c00307266080051401c000075164900300c1d0030890600155070703001404041e0b500d40603200c00110303010040600b41001081b41000d00140009840a40d84079541c0c401141a24000c0310f04103d58010071000f1141e483c8044030003505a4810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 261612041 1250 261610791 261610801
    0x30e0a030309111f02010b041a10201b01030b03100b0604181505031606030504060b0d060902010f0302071a130206070605010602070b090607030e0303090a03150501060c0209 76
    0x81d4104182c050b008104005920344901c0101d20581d0091503a0b40a400304d4203e400b804030b41c2030003008110ba0301160288a41040100c4c0b4041c000605e205844c4a4225182c4c4429580c3c040c0030f11a405400080408240601c800c03041078869181000200d812000e04502114960080c0b080400411010f0003c04c0340a041742d8208004081c000e410960103241440006001e08001819410203a1071402c086903201c16510000040c5034a90000e84c401d030001300d00c0c03420702410790410b80c2c125080c5180220301c84e00d40c6d0814000070036a41200540003048a4804802d218558100c3d2884601c03c0e60f41e001c0303500003000214102d02031900300074001e041c406a80b08880241e40307041504042480c108001c031501d04e82c0000c00e42d0340515400c49403580c6410041000c103405000300d400401a1103007207482d001250300042c4045c440e1803030090500c5035550920b0348540b410019240701b4000136000d0301446899003490107903880e80c10000c02030681400008502c841c03144071f001812076405000c0c0300407a00c40c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 261613291 1250 261612041 261612047
    0x6013009020609030106300305030f04020d0c0308090a08010507053004030c0c05010503010b091c02030f01060801110f0406050703050706050103080309010518060a090f062a030e0a03 80
    0x300a000d0307a000406121821580d0303020321488008044042c0c55420901d01c01c242003034400d0121140786034241100c03009101280d00001201d61040d480d114100490780c0c1d1784000341100c141d00c100501780341002c03c4d01000700481070005081e4a03c080710319421042d603a842d00da00f6160115055000144141300180b942000f20f0341003070705051030103180d00e503a81c0c0c0400449501c0c0400c54044d80001c50404510050012891a00300508070a203015403556050002485c5144505800c25001e8006903442c0d9400360405601c174040c0c0c0c0e500406882c1d012414a000c0c3c0d010341103034042c0c44980c1d403800c00d4607400c00908204030350007454a1000c2d90308282c601001540d10b504401000d07020b1220130000c04000501c40c0c03003803c0c040c600c00c2089c5502e03030400d052420b003141c10040825040d1b245085a9200300c0300d0004170564010b09104000c04c1c5c5802c075107080302070081800d00c003c05160600385040c10181c01c0141501ca000032074841414185000745086090b150080d00d440c0ea15081424145d0110744 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 261614541 1250 261613291 261613301
    0x8120c030c01050a05010501260105060706092a080a02100531031a1b09030304050306040606060806030d09140d12020d0306090b0f06030912030906060130 68
    0x2540203403828459445086030945600300d906070314081e0359200511103581c0004040725a6560100d810801c8a024001c3d299440b1060003072600c00d080c04140c00301088903540080c5040c643c4030480d0551524a020303a0351018850040c50050380d00c0022002c100b001c00010f01c01c83c0c6503001011040500d030303010010ba800d41e100c07041860b0010350000450021881100720407101d4502580c40500441c51030520300f4545510103070850107200311320180984003200300d5400480410020320300b030350740d08200006859403140d03a000940502998042000388611680860300f20760b0f103911264420f80e07075a010191076088811030000880c0310f45606100804041218400c00800507000c940080d580fa00c544070280420b444000050380a00b01c0b416550340e05000e000d009050440c81841030b501250700203003010f410440745d103005283c00300c00100c9000041120500344503800c10015500d003016005242c40c1c4c441140c0c3c8901050307059a0000300104925040c0f030f50710124800960801c610360458101503c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 261615791 1250 261614541 261614557
    0x120b0604030f0507050411090102061b0d0f02030a14060102060703050a1812030f11040e042d030207080d0c060b010e0306100806252307030305010905100812 69
    0x484244000310000325078481c20000580aa0000c1c004603107060200004d9500540b0304022411060120121598000a5050f0403540b50700030804041e070700c000302704054041c400d49000381134200102c864480340c40342d0007180a40f03001301c0117026581104d5001804540262803241c0181d002c0f03000070b013801744298070281d0400d9901d03001003401c110303042c02d900703440248032000e60344071442e00f0091a8640e0544140c8041424041c8103008207050406018614019885070503285114200041d08210301652114800505266604070360310b51000c40b80011102a14110050f1080e000f0101e208280007800d8464682d003655250111a007958070000030b0306c1d0705071302a414008110004485642c09100c3c0700d10452010780c030484620326080c0e2591602401500443d6295640507141c1c0d0410810340c40e945c81540c09040a4203503c3e03800d10714403008a003900c0b65000ca440c01044aa0030103a068101038100e800da468180843d840d810b40c04409560f07984204141507200e100094800750b002d40c003920801c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 261617041 1250 261615791 261615799
    0x12280501060f03110919050a0b0306060102010509060714040807120209070302070f060e010b21010c080402030d051e04350601030b0718090c0f140435070311040c120b 73
    0x845114012101f9540d040c0d0f00c410280b501c1d0256190320381420401c4582c841004d200034892405c110075495107481024042c1c2d0100f04c1000c904018481e070300e404890007014100d0480704d11540d21680c0c03650140e4280b000300d104810300d030003003050b40b88039009a4040c20740000340c1401c104090f0380e0b4000200300310103103500e45e552a10740802c0c041c2d46100c2c2c04001800b2240da0400c0790303015044c000342141c40721400003080c80300b04e4090102507200000c900c19804000d0a11aa860135141010169028500741c840e0191800090100351107500c0c5426030115030004203000d005212104642076030b0700464680000c50f074002401000890340d00c9080503040000707410303c1c5218031902c0101045200c41600008101515a100610070b00c1d4094600c00075542940362900066641e0417014103c3e110b14800c1200075510f60131405c980c48569010040c5555195180d0101422040d001c641c860103244000d9030381600e62403240c12203040c2405100c20700b1207641d4516522100c21200c41000b070110791741d100c0d08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 261618291 1250 261617041 261617071
    0x120d0605030607170109180204020d0b060a090e010e0403020c46050d080307080603031c0f0c02010e0c012708030705240612280501060f031109 63
    0x1a0307202400381501034442d990350000220f0420b0380700b40c5014010380c00035400d285844051511204101200204140c0c11100540c1e0352100501840140c10303180015640f105c00000c00001d05a004a400811281607117035030a1036aa98000460310510308035008bc01603041000805814903040c0e083c0d000000d030144011030010001e01d080b404c0c201c4908914940c0c4a403516098000905000c2800e008100c200e4403100c80390007686c0c4014250002401d80c400340303c10721010903d913a90520a0300c020100d01420b4000316401141c80c038000d8540021071140e81413619400d403842c0792042c007034a150642c0a0700200b420758000c000454800702ea0810f03007408211a4800c8214000720f03a00d01c600140b185100079600c81109041c00da06180307511041c00040f44ca03440181007a09000d00d01298070001c00c0f00c032090740105100403141000c1c2001d40695441085004890358540401006800c0702d000d01c000f0803029841d02c003070f1620030019010240030070780c81d05d40852980c80c0c04203265a00048032500b80003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 261619541 1250 261618291 261618299
    0x5010b030c1e13060e030a1109071101050f071b0206031f05120102031021170903010c03061a180d0807060905010b13020909070e0a030c14041b02120d06 67
    0x35058218080c0341448030803c68041080c3c2e5404890b450083c1d20440c003820320880940e840c060b5403032007680c00900410360840010b8482d40601c01c82e006480d01d0718028070861030140ea03043e0784c2c0507017182d1400110f09003100c00d48107444c00c0703a4452019607025000d545152210b00c040d0710b000c0340060051203004c0b11003e0101c0c51703446103484290414076840025880782090308402a44030001d80001c10300066003a846400400640050303240c0541001c541516502d090b078894606108462081c0d400d5820f005812845590650003041140c0000d82641006440c000003a8040e102e84041c0e1945d40c040012134444034500040c0c6042514410202d00345040c0003030713640c0001e81f103c4200507195a55255100802d86c14840d08040ca8414221070442c035061200740094410000503104a00704525480702890030f0301c07400f8810f00a0754020440440d1180e40b0910001a00d070400655406541404600c03241601c00012003150480c0c00d40250000c20a03400c6400c0690b000b125400100e141c43d400001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 261620791 1250 261619541 261619597
    0x1801140c1e120108010b010c0c030b07030f050f1501020f0705040e03120f0f1b03070f050906040311540a0b03071514030406150b1c05010b030c 63
    0x4281c140e114450036002e90315011429003110751844581d410b00c04810400030008101110900c140d940c801e5000c4442d84400e002200184ac0000b0501541d510707010600c080b021032801990712821a0700040301450003210300490720b420744050045010340c00321900388080d04d002d400240d00d01603101d080f04c0c1000d0810450114200003a07030788200351070301d05040c0010220501e200030f500c0042954840903552660b95021900e2200502c00c5040044c0030f001115904d1080007201e001c0440106440c0c0c80303d071a804c181072044090741886200700c0c4100e00030f1001192140f220307075480d499a0096514915000420541c0703a40c01d201581e148001e0704048500c08103c1c0300c04a015114280703000034a411900141494803010b0380120b94614040c5004819850340002c6d0042070307240c40080c01c1e840762030301e10340a000f80854540103080c2d14280c410200e10000d001010701001014101801100c10300701084004560b003e006001c0701150030000a039000000200404181801200030102251241946 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 261622041 1250 261620791 261620797
    0x6020306030f031b0606010509060414032d1603020a29040e070e030f060115030e030c011e02130e060607140705040c14220f030b1801140c1e 62
    0x884040d004040010400751301c104080c550000c1e0a003055031908a17071400058080c01640b10355203a669513034554215586045c880d500d00c40041900c14441245205501c011210350450700708450721450311410036140701c0018000440750003078030a0b4200c80c00c200501d42c11002c00d00300488600c5209841010440d5490001e02c02000500e01040060030003845c000c00c054803007880140310ba400103402c0400000d000c10010304403101048070350101c0746010300036400740080194013000d5010106049180e60019017240084a1005440c02c2c045000d01040604a00602048003000000c0d0b0310140300082c81540f0680e04a40c000f008103061141c10340d54040e18035051100c40e42d494210344410042030425005180420b0b0381410540c01140d151155030080c0d000750030308102d4910a032480100c1140c90940440c1c00340090002c00c80041791a810907840b40c0f40d003aa0300313100040808201c16465003041c465081c4094910300704c601e0a40300c4400000300360700030303517007130980c506010404d650158034078001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 261623291 1250 261622041 261622057
    0x4030f0c05040f0b030607030c0e0603010b03010501140c0a020d022d01080c0c121e040b070c06080c03060f0a09020c160501020a0804151e020a05060a0c090306020306030f03 76
    0x100303100080c00c1405100c2907400c00c1e1100035510b8141001c441c11682c0101da01e5503c80aa4035002800c250410320440c1d00380009500e59801c010f0020011420443c0d1200443c161130b000e0703c3e101589403680d840a203880c443e480b0f80d280683c2041c445c150052421561003001940014038100700d5010710780b00740c640d030106200712111804100c2030003203d65803c826081c3d44000244e0b4200d051100a81640d034030351420308403c200725080050b9900385040c3c2410b00205503080c02c0700c41511542c407181c558039254411901a620214400780016059208114152040e00f0302c204403815615000c0a00030000c000c1194039502920803400440c8200d8188050900102c0030002002072402e121502500200c01e030700070a04541001d03c00c8404205a03400311806c4520504078090701891712181255504c450340709030580181c03000c0d0609031940d40043c9906035540076a040e90401e441e6000d81c4411501150742c1c030300114040d400104046003040d4050b590103003018080e80d1a0507100e1224034159403048003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 261624541 1250 261623291 261623303
    0x22812022a0a03080c1305010c080f030405060403140a17070c0510290108040b07020a0f0c08151501200a0309180e0a0b1807030308090d02011a0405060604030f 70
    0x2c03600041c19409401c050f0054a000200384c50003020b58003d040d60341e4580915410711400e4140401040210021030b1801046542519100d0030149822030700c0e10b4048d2019000610055540c410096031324040715002ca030b250f2260a94243c0b03400107002400303402003882081c410034002c01c0021440620814002d40c0110800040710301c404c030a441040b2060028a082c0d0910801204030181d800800a5802540150f02100e240c0d4400c0f200324a4240d46007802003051043c0c012120400c09044014800d071203400d400e070751041c8191071030010f01d0318085940d10343e80549441c41d40703507550194039075500b441301024000d0048202d0785a1503117040740f184022000107100501c01c0020510881082903880003032442448890b0008150540d504032000d800340c80704020703802280d00800d40350700c920601c000034829a405150b403400c1c06012040c0840750f00c5a640141036103040a03503c18440d0314100740e40346811580341514a0180310041400400341d9030885c0e4100b03c080003066110a040005070f21642e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 261625791 1250 261624541 261624553
    0xe0f0610051504080d230403060b01030f05060d03050f0705031206010201060807120312021c09020a0609050112050a1e0f060e040803060f1f03022812022a 68
    0x41d0900044038000c0c1016441c089050200b400075080100c1d003007003026907900d401e4001302111119001c408915404601c220a40001c001007007086541114202c5d51090f2400c128840140c1c101e8401d03907404481d030550200040070b04000090240000e880701c0e22003c100141001c190307640341c6185030b2190401000e260000020001c2641c2d0900802010382307181d0014024035494100c04618448030f0001c000d0a0007110000204c1005c0250b0598148007103030312260300021055000000101b10744101a4002c4051190200300c4500401d040021508180d50f8105101940700c0c4480052101414928000e0b40b50020b0180c4100709030516810030151342000a00c1498003601d400c11103130036a00c01d28041881c03900b0031010444400035641e1021040d9031024503007440c00c00090410b451011010013115040f40000d4806074558007802070840501c05916018104a44080c00d0b108088d65100020304081c0c845c1405420680103440f03140390005842d00124210400b800c0700508000d102080b0f41e00032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 261627041 1250 261625791 261625799
    0x1801181103070807120213050703050601030b040209061c0e070602060f01140f010c0312060b090901140603180106030b0109020c01050a05012607050d1a01270e0f0610 73
    0x8030010a656880c200c0081014034601803215489030035601ca16903507032511454030000d6445505800c081562443d50810a5190044024004003400d0b204d01d40040e00e801d10003065402c00d8400c807452144000c1c011401d01171010401034840901180301002c45880f51504002600204007202c05000c06401521840c6041c1c9400010210142d2001501028100302c0c2a1182c99500103110311030028a025416200903050640d5400c0e05050b514801c503107840e000041c1118503070007030040c0c5001218403828907640c8a00c1d840980c4c84044030300b90300080800c00700d5003140b0721500d501000c1c4010400400c49560340c4c4c07180030700d404090b44000940758000400788a1b0280a20415070300c50065102040594103003045c400d007101c2c04040e0000040b0084039042e41940040150034003c00c0020010310075a071852400341d0301e2004c103c0b200525210084004200b9000d0365200c400c607084626003240411000e10b480102810107944c03000a5806058183d8907440d00a1221901c52454940c1c01d5004510b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 261628291 1250 261627041 261627053
    0x60d0908040b0a1403040c030201110f10021809090712020a1203080a180302060106030f06120c052b0605151009080c0a03021e030111070b07020d03020702030d08180118 74
    0x90840e101c0b000840170010000060494901e04081d0f940a20341102c905452100203417a0041c0c030800580c0e0b500c00caa41482181c5120340003040c0800340712038110143c00d0042c080c42541d050940328100b9a800c000004d00c002c5150030130b0400d01c03d00040601c5101681e03000041125078400c04180d0000b9a12410030042000301d0041f040b146991004032010a102620000d480c0c400c107000314802c05407510245003c0d1010b03a002070000d4115645100501e09143c90082080c200f14880c45005841482c0316003040182c0c03506503600298010808002c05405907200002400010078081014002d100f151982d926005a8510100e1003512000411414003200750714009080122030b02c5112404020b10040c0c030740e4a4941c46840122038011041c20b41880003d000d0a06054441d10908010400400784030103c107a5138000c840765000e0b0350025a21010880580c8241c44010750503502c405030840ca081d00c902c0d000c540c0b010304140e10210303d22000051a080d40d400003006608560390400310014042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 261629541 1250 261628291 261628307
    0x5090904030f1701120b04030e030f1c17071103040f0608060301290f030a08210a0603080a26090a0606080a02030a0209090c060a08090f0a030e060d0908040b0a 70
    0x20f400e04291503035072424090a0600e0000d03480140080d02079000304003010700400384242c40c0b150080545040b00c006042450350b030815244d4402026100503c420f03401d40c060944100c4031203c2029030070a9580e0071100317407100051070400f06030790710041000203003241c2018042c0024128039580c1c28040d0902500b00b50941e125101d5032202204d080000b01f000119020300341d426140c041c1c601030f81007030447c0f0020b410200d0380240903140500004000a605624405c2d0303100e80c800d81e244202d16034846c1008002221410300004160705410880103c0c0580985607003407036281c4090210804681041c50761080c90740589a00e18640d218030a41c2c07040141a00545000c0c5c200c0000800710180a5000241d03200c001180107809494900d0210300c1e802c170300748081d1280700c0020341200c0c0c0e16000310f03600415029080310030024601070041480b0f54201c020511681041d05a03842140f40e8050b0404c214044c0d004a01c0e411015540d81080c9000481e200040c00c01060030a0f202c2d5185c50700c40d000549800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 261630791 1250 261629541 261629567
    0x18123c170906220803010306021201060206010303120f0b120309040b1806040e070e040b040c0501050306010c030806030a050a0b06090708010e0a02090d0221100903120c05090904030f 80
    0x510001c01401c020300140d00d580c00814141105800c14540b2110b14040129050260807144000000300c24000350750014802ca01403511440b0b0315a03a140c0c3d00306e0729024280030080c0010043c07240b98100800503000b03c600344005101c00241490040005100800301680c611141c0c1c03c081144101c501c4c080c896201540710503645100300403007090161a04034001403106110700e5903100c85e48100300e01000044003604102100c140c0c80d090500740016054802c071021200040030800200c0c1e00e51103403090328081c01043e1581e02c030310b60b0a0f42d400e441e4043d005001c160035215000312040402e104110240340740d070041507110070a00380503040c0040090018816000d00c03183c0300041080000c900700d4558000440308006071071b0090f03980040c239800c0c0b00a001035032211540405001c5040648002e8610216620464410481d4032000d103042c0c1e8003000018ac08901d030b00e00030f0401e240c4207030010310030310559180c15464041ea4100041d41076038181c40c2500010290310030014041d8220a411410b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 261632041 1250 261630791 261630827
    0x3051204060c0f030309050a0305030a050109020a0c12021603030801180509031b0106030f0b07020d0e10030e03040b0a17060103060b03040602070c050604080102070618123c 76
    0x1030304240c8042e00c0d21140100041c6000b6100610405051190b0b1200040c550300000780c81011400b03040050031034005441300c0030198544000041c1a2032184200d070780f42d52032915407c0030000380343c0f035446092110445e11801d42c0501000c0d5407195408000030000707188207450b0303001d00e541007000c06065494028400990b003840c140900107908000020ba60031510803043d928442c226281c8081c0c050000c50740010152445c5400e24030411082035140d80c4074590303d600312445256040f50480315226800c482c90340000d1500300404040c0d12981200680007850ba04407458103541c1d41e04ac99807544000c2e9001d001a05a014403411031070388005080d0800001d1800b48074103418088800313207511001c0c03c0180815030000d0750208210094a0400040400a00098030383d81c1d1604486c0c080e50105404523a003c1c41c0080300074a8000d8619001002900004200e446d041004016243d44203244002ca114545400e001d20080307000c942464071601070215028034280c1c0b003d4014090b039407a0115101d0f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 261633291 1250 261632041 261632047
    0xa110a031e050f1905010b01030b22110309010903090b1908130c0603050a0b01211d03040311010e030d0e040b121911030703030c02010819090c030512 66
    0x8121a1400326040011401e040440707a85030b440c2070740c6444154102200c45024800c1c803038014500ca040b422030b146020b40001e008203c144030044040302d041e5602203501c9411200120410801420640d1213101e4104000410a10b24800f0701c219410844550405070345071001d500403d5403100040c00100100b400f001d0400e4416000b01c64590349004070601004644800904500031800540750995040072034140700f1307a11000000e0250400b01c84810405003070140701e480c5035220301c0d044203043c190a286481e0b0031102d00c0e80c040c098401000d03800901c82e00102c40c0781210300c091000f80015885505094540c0f00100005032580c030503003109501c41e4010413501080750b5000002840000350440d030010f4480c00440000e20140b04211001265100c3c040c07928003000d200903456003440b0300462044140200203010541d40305001d020003400180390059480055004611940e0401682558000180c8800514400311040541d05448000114408000f8010b052011051184850041e185 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 261634541 1250 261633291 261633293
    0xf0d02130b0406050909130209090f060c0a0e120109020a08030a0f050711040914010608071403032d09040903050a1713030806030f03030c0301060f0c0c030201110a0209090a110a03 79
    0xc18040c01744942d001c1c0002c02d0005200e510a4039020000c0c5a0040c0810040e04040007200d5030340203c000039a8040c031407200422502e001d54400e407a1500302c07a903603d19208640380103011030520a502c0b05400741d925404003600698541c41d20102030329260000750348070040b480d40200314480b81d0380710000f841010440c0c0c80100d210a03646005103001a01c003c43e4000082c0782400049510072081081c1d940b81c6400840d8031440800c1c040308840e03c503c2800c0c3c2d0b0f04001c004254891084011300c1451246401030f44400468042940c4207142141000ca410400b40d0740111341903802006040780024400a0618001508100310401120700d050107005a0701d44600a4182d00358400d00c09000d0000c0000000c6180d075040040c9034000c0c00d0b17402034a0303c904000f01e01040c0740c0c20030b0051034041910346440c0850130740f00300417901d203064000c0031440c1c03618503540054440fa400128840c8150042a45000150301c408013454003070b810020040000300c072242812341d000050098454418006504204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 261635791 1250 261634541 261634547
    0x7151b170403080412020f19030212030f01031b0306090605192f09040603030906020f0a1a06060922110c06010303050a1106090304171c050a050f0d02130b0406 70
    0x199120317a11005807800c920031850144d10308110640c0401d03c07841829968406410260091944948603401f11045c01c454003040000364001151f1443d01140c05800400124241502e60307030b0b0601e03111023840c40594a80e01d8940580d419400140c490580366070a00c00c10440c0190b16000d0110070602c108030b107150881c013018040ba100c000e81a0040d001800e072283c0000031000310b0b070f414100200200b21fa544d4038070b0058200750041c85000094001c484035190000300101d00c07038540c143c1c0600c3c9251904940410300280b0000500102d8000d0402e1000051503250142000b41404281ca2070300020762070050754100791412101040030790b850600c03c00070140d1002400506595060525546585251500301c41c40f0742901010803503032085200740b2810090206c003c20940303294001c1c9022412000801a40e0b0300b088044034a200d8010f04040c2c501c95200700c2c090f1202203810f151052600c042a401049250070001e0ba06085030741c00140d400c5010791802118000b40071040300036041601d00384010f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 261637041 1250 261635791 261635807
    0xe060904031d040605060d0608010c0507050303060d1a2503090c050603070c08071a060a050102060f06041b021006080a030203070b2d1906080309010507151b170403 72
    0x200c2c803500c042c1001d00c0d29640d2680c1000c805010701a2105845403800c801c4007000c0e04441c4140c0085511b04000e0400407407180c401c8500850300b200086145031030725828000803d54445058a040c00025400c4caa00d4114001d003e00881c628030110750901248005030340e007810100020780c241440c019001c070024090220b8001100d404480c0240c580d5100d69090301c250b81555801130100340c0005100c0d04204d008558144039200003003168120b07945e0340c011701203145228000d050140e07020800041c0880c00100c81251302040250000c1200000c1c0c40b14400301d0107945405201507006003c001c103052401d44a0100103184110040081c0d101948000e92070303104680015000c0001100010015007500708442c2500040741c3c412140c03902240d0108030003040139624003100708200d44e200b102011003402604141c441c460302840c6480440f0700199182d42c4001801c0361084088070030041085054800c4001c403062520489510055010008212100720303030b4400468001c3d0340074040840d030300204e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 261638291 1250 261637041 261637067
    0xd030203060a031227180203070c06050a06051302031006200a060b04050f061f0e090103080a09080105070e010c1a0106320f03040c030b090105010e06090403 69
    0x165252520381c0440d4001c8215040502110300e080c1d94900c650794400e40c0200541882c21548081c00041c4c6210510460a8803841d60241c09480305890400140d900840e0032260900f00700001e1801503944c2c100b0345c0d01c1101c24486440c0d03200070401280c00c115102108143c41c1d0f0508500c5e514001d60704007603d03247d5008e07603000c01884441e004010640101103c2c0312820000440d03103032030142d20340f50028040080303c0034001c5082030040391550614440050144000400a450591041000840280c501c0301510200125030b094240a0384446031564041c5025542d50f9640f0824003001904100c9168000348a6a243c43c1c1005225a441500c403135001400b440c008600e0b50701401d010442c020300c0c1c91064200b141203400003071529040750110740038095040301951940c3c0c440307c400d803d0f6042406600b12203982000420302010030a0001c0d6070240c0704201110409480742c8894101c000112011152695102c00500c022a1700310304d01940310074104c909000914260b134004160409241c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 261639541 1250 261638291 261638297
    0x5040203100c02070b0f0910020a030906030209010302070c1d060315011223070611070e0604091a040303090312050606090108190e1c02010204050904141504050d0810080d 75
    0x6402c6405442805214010400c01040c035481c1c492040b90a11680d0181c51202e00c150704601000305210300100c0c800c030700d454068485299262601c0c0d0254041e601600f88141016801c1003180c1c00151854102005003940060302c0c9004030322100c4c101901c0b107010301001c1c882d40c0904442e51214107203211540c1514086401519092080c1c0f50402105907c3c907000b92410050003460200041c0008101f0100c0c1e81035642c014400c4440d0740f00944800090003551240b0448000040860615412244040307101e6a48421001072000d1001c500c04000e903411000291600c0e100d00506500035505668243c1c0400204001e0030700000141c520704c1610019810b106501c0c4c00181110b0007007621050080f043c0c4c100b072088542071005203848007603055104207400c42c0c0000311803009105100740c078152035014144440703079119501d94942c4900455a155654821200c0d41c0c80e00c03140d04c448040c0120301c9000100950000441c0141c203488009083c00d491117040d2104208100300004c9140840100e41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 261640791 1250 261639541 261639551
    0x801121103010b09090615100906050f04080d0801090b0301050f0f040201030b090c040f080f060106050d0e0106091b171302010c0f030207060813020a0303030b0d061d100504020310 79
    0x240200b805050401d95030303544019038104120400c100410100e00c2100c40100420607218039800b00180307624070b101d0440025981c00c00030f01c0354074000c0340103200c4041401e001e142230030b946250481c5042c040b03400c070400050070800104140b03a4280210310740240110020f204a2130062000da1100c1d00080a030320418140c900800e055901907401611807400103804600035280c08403039a162944144146400c00307800c008001504080458246400380108000d040703103900c0c0040894060f000f8840845070103075a826104085003091003990000e010036440070038070440384140710a12004915440041c410b91003480780c6404d418042d200d034882c25080c08040d54485600040f25000c0c5040c01c0140280c0c0b02a10910074150001140b6085807040da560104a503100400042c80f1500800025004420800e0520019000c0e4002540000703018201c001e00e81081d4850000f55002c084000c02103026840114004020502c10700100080000084c40b050406a000c030707584408603502140150741e10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 261642041 1250 261640791 261640823
    0x12041a030703020c010e0c1003180b0402030708031611040c121d24100311010c1a04060c020706020102090a23060f0c0d0908030316021c02061006080112 67
    0xa6415550460000720003040845d070900141a691f40d403c920315071042007118800103d01d4030a028103100703a5403055088455003003d540d80d056082028104981c0740c001e103440840e189400300043c00034903040301166403400a0074200700c007105810018103400b0714146800a06c001e900024034101215854400081e090307200c070105c81f1700b40420340208000e400742c6101c800760350744000300800c6c1c2c80044140340d90013a00c503207021030b02071361041c40000c2c524810f03070048140a60088010328299802250030710ba03410340700c4d031001310f4a102c00c0300d00300c40d5282e41d0100102040c2c1e040102d28043c204a000840c6401d888000103550402070b8031883d004008101c18641d62000c1c0c10803000e9001c400039146a860304440c0007884207a82009001d0110740c4615442104a0751058024204850908000d1491611550880100100192023000640c03003407070000e000321500c003c00044104180c0c2d010b00254249004131141e2500d46620100402400d6401400381d0708180315041501703540945041d031070002e0303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 261643291 1250 261642041 261642047
    0xd051506040b0a0b0d05060f0123040911070b0c0c0c040207020f09040305030406290906040b061605071205030a0c1a1303030b0d0308010627080f12041a0307 69
    0xb0103203000390050010703840007508404000103488100900300d0f05002c1562142c040c000407844104d407190001d25202007241280f4500b01101342e096860003030700c614141c0c076568181c040c4c440300750144d15500800120042402003c042c49074208407018003007440e00258149299981c807000000c5481254006662401c6581c0c2c00c0a40a5552001d4484070b04d030703d02030501805940044038140c44c400c0c244016440c1c03405444103450a861181c109003a035418100040c0103030900e00402c100e41141d51041e00c4030859403043c004d48400401c3c000524441c20080ca000e40c281942c076070000c031180b03417010380c1000000c8000c41a90600901d40ca0000300d000399500b81031000c0700801c41600c8100b40b0f00300500451506442c41550180d001352014010a0102d00074400010b28212014000412410051107120310909164030b9440c40c43e001103401074140d00560602205981c08507005501040d60440100e509020f2214500c90f90340707040e4105807514000b07091040241080e200f82100001c0041d00303541c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 261644541 1250 261643291 261643301
    0x91502010603060c11120405010f0e270a1404051222090f0b0102060f01030212010f0e01050103030305071e05030601110f0d02060105150d0903030207020d0c0e060d05150604 76
    0xf41140c024403820303c081c1d401400249803074030441900d00030700c1c102802c048107a0040b0b408071001a910304482c030018544c11291a2102c110481d07008041c0c4240b8512404030a128007160441d04079543c0180c181900910304880d0030501d0a2122043e04082101040700452100c05250303030b40d10005d42d12900345640100c0c0243d4130b44c010200f2050040003148000459100c02605001e60204119450f02400103a03a42c0b5004c0725203000314604800103100500341180714041d18183c1c98008602e00c01440c01e00340654142040c1075240c2ea6452004100341075041c01855004000c0d41800309242c100040004c004103076024550003441400404036080da407092130600400d81c1c01d4001e0f10700d0642030303112032a100d00c0c401c400c2c507005100f03440021619181801101141c00110590343e480d00070095070010241c080501c1c140c05140d401d208a4015841d6042d41c0c012545c03003129020304090820368804d165090280185004040b42c5d000407001910004442c0d09612010068071500c0c0c0e02c4100083c0600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 261645791 1250 261644541 261644543
    0x10b09030109020a03030e24191e0c0c090603020d06020a020c10020a111e0108100302150d05150d0f1b080c040608030f0712032309100c091502010603 66
    0x250700041c3c0001403581c0060301d6050007c003150720110507201c0f80300d54890340901e000c101440c0720781000500344842035070b00c42e80781d12001410f1200d00c8846c0b0046407101c1140001c560300200d0040f00680c0200700d110000c8401803c02407000f005814259008603010300310b151002401680c1c002210424140200a09003500398010491500c064800d40025100d801d08001141c502c51940c104071082e14140344010040700c40c00402e0101200322400440706d04a01400c5002000980f200200150320b41444801c001d641b24a540ca68601048012200700c1728018500080c04081004201940c1e482c0c900a6a07000c0d0000d282201e01d107054108204d9110107000f500c103950061140000740f040011a40030016002100c040100d02d580f910075503104c1c031402c3d00ca03040c6944104421000500e81d850252103000c05403600180c415484a801519252203500100c0242c54200070010001001c225020800c03100690910000c96111405010b60149000f8203803104146030107003801078401d5114100031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 261647041 1250 261645791 261645799
    0x130203030301091a120c04020a11010204030c0e0903030c0403022116050103060b0c06181609020d060902070b0c0306010201090c03060507090605030403050f0a0e030d08010501080603070806010b0903010902 90
    0x20350b0b4404000f001440b540c01c0c800b403040700410680c041807802c0f00380f1094604410010300030086045003044025400f41d946441408450014450324030424030240001e1840340040c50201400d20711804540500104041c0e2580e004104203d140f5103a5002c0d9000c40c0d506541030111811306c01c0e0900c0c80c3c40803007000072006200d12840d44d1350a100014501d42150030031703201086007588805014449200307040c060356a80d8081008038452003803040056a1841c1c1e4001622041c00d14408a800090300790b5008507041ca80121740daa042e800540b02d84402003000040031480d2240580e15108041401403100820303400120018500d40d000b1b4020f110016071246074003044949901d4600001c3c00c05484000000d0040d01e0045081030007202140c0c002c5400da182c8609020841310440c499520000d154020090418002e6050307440401c9201c41d800d215855150081d0b05180004102d44d070000c1c0381c1ea210380d02245003001483c2010410505545061801c01c0c3c1d68840c20b00400e015240d0b141002b500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 261648291 1250 261647041 261647047
    0x90418020402070b040c12031b03030902030307050d03110c0a11030c040e0102120f06011b0f0602120a0c020304050f040908040b070b090111120105010503060102210409150602120313020303 83
    0x4c100f2103012031441a8801c1840d1105551a141d00310065001d88a0040114409072141c902c104164140030341094443d05d404a281641580070a0464115210131241a4040c0400c003142903014000d00f00e0003411061080c0c20700744100340460382d41c0d00b04280030b007106a2a40000d501a00d050089075040c0002600600000d005158018001e6001e039901c0000700c240301d0086a4440c0341040c00500405059681911611250940315014000040c0c11620103c02201c50000501c0500103881c1d480701009130740c405403800c45407a500f03442403108403100719001000140f0145e5142c1c41500c2e4000c2040c2c0d00001d0b00070961034680428419034000440c114808600c00041001110105200303403240002400311403804e42c2099002d0041781620400f06035000014001544928055548900144103c81600c00650100d1450500d084e22003003013003000090a020940d4079001e14074407803180c165031030303006450514000d458070300e50010210707400f0000002c42d50300c84042c0d80140b106500201940d41e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 261649541 1250 261648291 261648293
    0x230306092502030702041803081909210e030f07140a0b0c0604032d03020906090901090b1005030f0c030601020f0102130e0a0203071d010c050a0f0b0c0a0509041802040207 75
    0x5500e070801c00f401c0303116504000020b40035811400c0761404080e410703209c0c1101a2250041c409030290710b03400c541c02e06030742d030020300c03010421441900c1000e102d820782002c00c100c00aa40103204200203c08640a640103401c40c60b0007000000b00501103440c1c110f0360080c040c25500c005544806654071130708020401242c000c428040106250740124420740341c140c0c109501c00d264201074034540107016400e0442c0401c1801203030080e00200302100c0d00401030340c13400b82000c00161941c0300c00e070030181c07207513039907040720f0004e41007200c1c03507094060b1981040350030361038440b04001410b40002c098000c680340110202d60541d008020450340c8207080c2c1c00a54440040d01346580000c44d0601c10142c2000b090004100045178a10850703005030b42554404c0c50003130b83e440503450303a55040d221080c10403e0742c01e901400301d075050000385c0c41c443c810b08100800450f40e0410f0010198083c01e48403414070104404106550044200c0700ca0302021348e40424980c83e440c02c0e0b19201c0140d000080d4001d400010450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 261650791 1250 261649541 261649543
    0x30c140304052d0304030308060a12050601180e1e031e09011202071a060a0f080a0203060601050a0f0804230f28060518070602030703230306092502 65
    0x7183d100f40305070400002c0003c90251040d14404900d03903c04035041000709001080c440c90005600180141c00d8903501c0d503940100070035000e030710001551340c0d412030f02c0103010319441c1060741c0017620041d1009111050340e0181041d15081104c01255041d07003086100d50180405005490303504c1200c410800781907605009a0004d90701071a50b8034000f07482e0094210040c00c00d842070b2101365810200040d032410b0044082001014040e060b607510001c41840010590700c032070125000b409103440070b080c01c0200c80c814145000c50140402d410700c101408200c020741e60106032490060741c2c03494a04504e0310381341050101d00703103a82048881d0114084040280e80c0c00060280b0900d030350041101d01d1107000b41104258004011003042c07041140301903d6020841581183c0d030400b4031032903a025210011800c1030b150117150350081d00035070000300b170810a0640002c140c5c500041400c50200c4009550520985144802040203209455203030202d02c401402c6400340c40d9041d04c0e00b11340c400700c1d05160307006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 261652041 1250 261650791 261650803
    0xd0f060507120e070b07120c050f0c040b060c0330040c060e0103141302010909141e010806060d0302030d1409070602030c0706030c1202030c04050406090912030c14030405 75
    0x4040b080c0c1c2410710b0254245030009016044540501c078041c100f17290f0355921482e0409108000781000443d02c4008085641404549032612400001745581600b4800b0700050740e00b49508107200d058180000900d012011046a0b10304485071b600d00c80b81250001003904842d8041500004000351004010802100001e4030082c1d0301c46450740c0d554000b44800440903104c010701111500351400000c01e84410b10403503040320343da205062068109449001d203004441c0074181c00070035590302000380800c0d19100c240c8260841504181c4100c84d40c186102c50b981c0f8a0098443c0d80241604c03481201414400c0c001c1d91551204c00380188030603545000c1c0c40c1c10084003502c0c422064002c2101c00a14980004111001e030240305000d01a000e2414005800820b0000038040502450000f0039aa140b05c42c0300070352244030340c5040207031110f00300414070040700c05640001c1881480d040e285004200d40080d42e0390b01421a00d0082411441c014089130703070703885c46c1d0304803031400c2000301c1480100000442d034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 261653291 1250 261652041 261652067
    0xf0f060204060809010216030806030a05100204061b0f080f190e03060702010204030b01030809010c080339071401110417010513020603010308130510020d09060216050d0f060507 78
    0x30f0560795485038041c41e403c17481070302904002c100300d201040e80081d0084c001c0320343c4410010242c0d01c0074500c640b56281410b420b0010703040302c0d9a0000c0d091000c16001000c640b041c0f030391a55282100342071591034042e10030110601030500f64011a4261448400c81d0866444941200d0b5440c40c1390042e0130040c246031010241c451003402400e000400c2d4134814425a0f04407074000000c40642d03442c1d600c4400c680c2d03000284071810089103881940200701590011401103030743c0608901c1858140d00480a0002692200799210f9032107042ca0409000d4803054640d9660001c5400c1d00300b4800000f110700401a81200e10005100850001522506411840d51244d6101d000340320540c0d450000301010f81a9041c000d5000f0012310060010921240c050180c072244408003d403402d403120300180c001c0c0c022540c15070040e882407a9400314194040f41c071400030152400141800090800c454406103441d014003030007003528040d92000e01484840c11401ca0303800050401c0103050600d80140343c500d41c800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 261654541 1250 261653291 261653297
    0x801180f020c031c02130605030c07022701050102030a0f050a02012d0e1204030b100f0f05100f1b0203101a09090703020f101107150e040902060f070f0f06020406 71
    0x550040804c1402201c403d940850600d020050a00c0010303240c1350400b611003664142e041c4405001a107a100040a101150303c168000c540300014262106480c141c10017411500140140644550881500c03889020141040364503003000c078108a00400c1c020348802a0039003a0415100c06440c1328042e0302049040a07000e00c84120280390042e511541d0306091441000c08101c03c00c0450711000009411801040310b407090725503504c20050040c6e0302d40d08000d01200f40c0040421040c07038420f88540b100170050404010801e81007a000c0d20a160b6000c0c40303001c03405404c180d8000c540d402d0000703010007c0309c03003001c008206403542c8170040e40380503403005401b480d8008013045406100142c40030860307a005141501080a10082c403070000040c10442090042019244c48000014032008000d04040b02d51800c0704078224034001d201040d0300c11100c1c001c61800c0581400b5890307440403130b00c02d0021503404943d1040c0c2858000c940c680100c0c4003404180c81800030710100017480d0000d00c00c030741d0155 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 261655791 1250 261654541 261654577
    0x610080106090b0d0b130b04110111010509071a0d020c030315180118020f16060f0c0c08071a011202090105040203010e150105040504020a0c20010801180f020c03 71
    0xb41000700c0d1594222650b001101c86101000680c030710381000c0c3c4c0054503482c89074030801651b42d070b2003102a040d50125001800e0080c42e00c25541c1c400d000c8111b07a520171000303000505106030309584404403401410102c03055001508001c4a00104031441148640011507a4070942c0520307644030342041c0c4138403688000c901c4681145d480d005098002143d00030906441e00d910b0400400f1406c4480960f44100070b800744100e0310b501081e2005400c0380401d0248891941041c0e00d40007040b5926001201e8409213410190300f4a40d9105000032119603000c4880b83d0788652605201e04290604202ea40088140400102d8502d00101110341054429035086400742d13210410801a800240140341c8826124030000d41c14944114603144491010305081c0d26043c0c0305c10100302640d0051801c9000300300c02140034010480381c00d110384142c02d80a80e1200c10b0710020720000b4648801841031500c0c440780f0580b000d0741d00100d90f004c0100c41e018541c0840d540d4428a058548030f0700a00303030001013040d0760303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 261657041 1250 261655791 261655799
    0x409060f0905040b070e040b04140601030b0a12030e0607020307122001141c02210a200d1103010f060f0212040504090302030f0d02041a0f0403031b02030610080106 72
    0x41c002c1c58011640303e011030445a641c004200e601d5000c40e2600381d441a180c00300785842d80c0700c91040303a80103800c0c480d510304245170040000d000d40752800034850292100b80c201b000803500c50000079003059418605440d6611142c00002c40d203000e24040071790b25005081002800c00b42440d146c1801038810028001c04495010103040c0c240000340308140030034420811300c403a54a009000b0022081d0071429a94028080c440e0781049070007144c3d100441030190f00c9029490150804143c0e802855420244072002241c00c280e062600003d035807031038015000c5001d0a40034000c1d0001d112443d1315030385894480d80d440900004582d003610034600401c541d10500e2410a01c04101c0281340241141920b24040c0341209000042003240c0042d011800300340810034841e00c0e208020a030204400c2d03400350b10b039420004100e486403541204994864020021400020518400d6804807509401c20340207004100b101c0600d001c0038036030000c3d8540505001c21145d40718060030b0344d09503006440200301d12521 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 261658291 1250 261657041 261657059
    0x111005040f080d0f020f19060915021b03090a06030203060a150203210f0103032303180d0c110d140102030a1a01112517030306100915030e010b03030409060f 69
    0x11303940800c00c5800007d541c4000d1101e600900c82654422000029054040d440b00c40c1c3c000c000a6481003120740000741d400c80016001024500d0200c010003452034030800380001481c03040c583c031032f1005241d00400080c605960b18020003000f0009460300785900000c540000303483c0e078808a0a1052030500c0e01250881e120b010900d10702c90f6489502d0030f40c0590031038805440c14011a4200c6d48400d0f02c980503400c040306441701550260301030b00201c1c10900d200f0440b40d03041010464541c800c11010b01b11410114100071607201c040305080c0c46560301c140341400d105a07520580214203031158000000e100801400e6408282c0d5600a03500c0180740c050704a00449803d2000440110103070700030751070701c007480410b00c2d40c010420804c80780c9044510350320402c00e0041c01d10100380a100c0e800c00b0042181c103040501b135038060546903103400c0080301e061001311070b03101d000c00486604040c0d855116500c425000d60240c241c0344801811291160b50740c0c10480058585801900001f1340c4803500090300d07840b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 261659541 1250 261658291 261658303
    0x4020a0e0405030904050402030316110301050f07020601030807030e04050705090907050a121a0a0b0403060b091603091a0c09011103032a09090406060e13111005040f080d0f02 77
    0x2e070090185240294103810400a42400362050340c0c140020050710b081c50a1980406c050144a07180c3c2103800c0100700308041c21070b88010b03c02c2550074182803c01480550120b180d50540f640310b016031345c88607032508040f1450310280e05401c0c1c000380340606001c00c1035003240c0a400104011a00449255940201210180604411400400c04001440b014600c458001d000300313560b69506c20b00c5112007900042c0c6510000e900c51007840740d00107010b00601c9030901075091000f1099407540d05070300f844d40c60390031741131002402041010f0382c4258902c10082c20f8011556004c1c0ea8543c074420b50f0500444480303440c0c0c81280328901044500000d22a1000d01206913407103070038149030700c0c01000c90f83c8140742c0c1c00390b42d0a907008500400400c00a0030960b01c03641828001c90241074001804c50521000c141d05e034101a20440b540b9258201c00b6000801150307080482d03042c143c0d285031114140a0301660540581e42001131010401d00010031254400142c140c1100c00c0ca544282c164580e5960603a00c41c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 261660791 1250 261659541 261659543
    0x115080705060706020f0714101b030f0209030a150b0a0e0609041a090d0f02030702030a03120902041107050d18141c06051006090f090906020f0f0304020a0e04 70
    0x10300903440410980c034285014100d61401180c0241c40e00741c49030800c02d0b01d540059400c445155107844802020542041113900380c4282c41b00401c8030454600702500d4416802542000700740d216080c4000d00390841e01607904240011302117a0314422649014201c0914100d1180e000520340116000d640c64002680e0048505605c5c40c600a61030303100500070040d030000c000b03548851340c111070701c503903401c1c02482c040c407a20040000c3d0012100c5090000d081010b01d100c1a42158414003a50000da03401282c3c0048440c8e140c20301a0800da001c80842d07000d07103e40c5001940c400d142c900304440d020304070f5000380082803244056424004440206440d5400340d411403003540140c3c910240000ca60b882901c0034948801020810011000b06004030400c0d00070724100c401a882c0d2040c412860141080c5801621113401c01c1c6081908203160800c10000c28070030f155451381c48541050621140d5812a141061150b0b500c035580d0b01c50901d0065154016103049000303450046c000501043c00c0801c040c0a1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 261662041 1250 261660791 261660793
    0x807050a0c1202120d020403150603024024080703141002031e010501030506061e04030f03170106020102070206030a1d1f0e0106120b041502040e0108011508 69
    0x8070820340c60b60480c40544446000542c410524800c190a2002000d400d821048000143c0c0d11810340c40d0070140200007009245851b410002d0510060352800c40d5a410407695204981d03600c0c2d9030780c10350100c0801c0c8002c3d20240d21030100030703100500300b1500140d0245d641c4428460151a44296088038070301c15100d500c0654002c0f00c1c0c28000280c103032030b4078862440e00c1000c440c0710b40f0103100b0010480e0f0050725904003003821000c60040c820a469236844c014103090904115034078244010036080d00c180210120801c00649404070106c0c04813064a000e10f401015035190006145005090132040c400e1804692100c9400001d2291050084642456015080d1400c540319452144007401c000e115100b0b20b004110458003595004105004400a04003804d080c00c0d12801c1c5200211902031444403c0c99042c0b813800d0207881210380b40394001560103007807100780d44e1341d40c14649505440014075642e11400064005001c900c10300c0b601d8140d881003402000010072200e20200303612158414110a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 261663291 1250 261662041 261662057
    0x1081302090c070c0b0301060905100e091501050d020a02010e061605071101020c03010c2609120702010c050a0c030c0801200d020706050408030a150b03150402040806090d0807050a 79
    0xa00101500d003d80c03054440380c040b90345540d51008250400d030846000185104e0b4200301503e4807500440c085101801c01942022104012070201100249410456902c006c00c989190b44500100c403a45d05280808544481803020300074081c0c4100660046c052180c000407803121ba0410480090030101d54071420b00e403601d00c0d80e4a540e010f410142850540c010000e400001d84c90a0140700902107250740c6040d503072000105059003011084001b6000d184c58201005003840f0002240500a2490101d140c0c85404030f200484605902c8003008100d401a100740794100040300302401c1c2500c0c03243c0d020030303100e940301c000380e038200c0348601e81c00540e540c40c44030740d0f040c2003035500700800b01080b034900c025181c13901c551940302c1500c2060b102250300e04800020064800164030a1661623141803500c0010a4a40f003201c0225000250699080380007102c3c00e402541d0f240c1d07044500800444041e01c8461400c03050154860804c00f00e803c010a00180c000b40e0118403410840384441596252710302 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 261664541 1250 261663291 261663301
    0xb010b03091525020703053706110d050106140a0c0f0203160f080d0203040612020a0905040515030d08090a0b06040f02030f1906030c0506032a090108130209 69
    0x400d22000c0d1160112000c43c00100c0c0307104191208264070090183c0003858070a00c0c0d480c1c8185070a1407800807a00d10300501c008500f40001818a40ba40005084808043c0a2a904002008101e029034698408900280d61000c9a4081e081315048174132030340303801d0031441020440860901c00c004082c000039002d035a01c01d00042c5000c0b5070400460000d0200c65551515848424206803035401180c0c0445119004000700c10003088410303416401440a0b500307180c0750401c003900c000454a4a503895a8001c10b03641c080a101d00c2401c0010a401401030003203040903d1842d01003d20780180c41d01900905248101c0940101ea04c0d0380604800c40090044035403644803202c201c4401740c20b10768010b40f41c03115104e445030203001440c0200701c0d4503007000c1c850030990401004403005c4120f02054505041040002c10307510035100742119400d07940190303295292400704010801c8942c0f80c0c820101004c100e483c0c10b110100c043d0070000d500fa21100e0303d94681e40c1a1403034854140c50020f40c00048100050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 261665791 1250 261664541 261664573
    0x2030403081b010f0e0c09010506070507061b0503040e04061a210c09070e010221040902070f06052403120f090a17060610081510020c0301180b010b0309 67
    0x59500b2450704000139026a0340c0c582c0308151102c0315422046544504d51031603d03840c02000c01801002c00b1207900c1c3ca440c0d026540c0c0e503103400c3c007403095006015441c0c5d110401001410404000e160340301003070381d03036a507107038420340c04420000c2e1070a4980751710300400c0f11071403080d1b0000d1112410300200301980f0b01c4155141c0a038000c00c502c01c0e83c400ca0181c81d0090283c0e45a080344140180e0700703919035a5800050a0009240c500c86000e00350503100440e10003d0340701c003078000315000d451400d03001607591141e509052807108409440105150b1801c010031140c1ca10000d204240308010004602d5295400d20800d0f07a0f5045841d00b00c0383c1c015042000c0c21000e0b4410008204070301001d8040300d0f1250340d505000a401c442c0d2600040141c20070000c0040c145070100040c1c07034102007400c01c05c00314101600d804400d403c0d00507541340035154080040b09858000c02c041403036410014006d1100070407a45200c012022a42021504042104000302e40241c4c0c28007964443c0b0401c4001344541e00c0c400c2070030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 261667041 1250 261665791 261665827
    0x60f0c0e15030705070f14060f0f0109091703070206090105060105090102030909071106040c0e0c0c0c0904021207090915020702130f0207060513051c050406050706060e090d08070203040308 83
    0x21014010100542c0c80019011000c074410705008804554990307c00031026402e2100c014402440010352008202400582c0d428070380c150b03140303a80005040d010b280341500194059488460150402001b00f00b01c00b1b41c0050300d148101c104400a00c00c580f5100010f44050142081e0395015810501120441d03061010641d41e001c803203440d101205203641d0081c07a08122040c0c5080e038403c0d000700740074099140b0966500e0340140c4c40100c0245442040c0c0c40c00c47d1904d800c502c5803481400e0050220701035581d07040207501c1004d140401d954485a503a49800e0003011450000c640301140d90090755812a00303072080d904100d40241c198140490b10141400040800100c02c4180030b50921030400490003d00c134152041084455840384800c0a0030402d01c0d052250b1947c610011101e9840c4501d142e100381901d0807100141401c075200e071464a0014003900c0c00d500110080044c0408016400c03400250b07200c424600f988648404cc1c5134920226101d00c03c2c2d00014010742c034200828007030101c200c020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 261668291 1250 261667041 261667051
    0x1020c060913050a180b04051b0607020d05010b031009030e030706020c1c0b0403080103031803030516080c0d020a1203110327011d0c0603060f040e19060f0c0e1503 72
    0x61028400c40070700f4090140903000ea4181b91380001700010482d040141c00c0c0e0701d43c40104240c0c0501151000100c2da841498070080c09a010070441008100003500035440c5140d0080548140345074845480c0b004100c2c001060700054045102902e40d4100810420142c1d2565405446d400300001c05001a60901c001980100c40c01c4019000101f01e50f00c4445006502c2680c0d01140d551560070000c29203c030fa004074800c00d1812600c1000000c0d002021111100c080c510b651030410720030300301340b172041c010400144078500a0500c03c40d025540420980c0f0b0321342c4242c02038207030403941490440840e1503200c02c442e001036017000410b13043c110080221118180c5441054090410358040600b13484080040d04550a840045002c840005020300341e00d0300310641c0c1c41c508624003000015010700c26010310501655450110000d03054080c80381c4040c03030508002482407603002d85800c000810300ba0f40313141041454413440030b41143c4240b0342d592006500509410035000c4900e403e6000b1740c00a01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 261669541 1250 261668291 261668311
    0x10b01050304080412050312071e1704150e0f1e0601080a020f130e0a12020f030d150b0c061005011b0b0c0d11040e070509150d021b0c01020c06091305 66
    0x250058608c168420521820203540c5800815130001c01760411814092407440c10300c01000e07400c05071035101e9030f220b036030080e04440f11805805651180c1801000300c1c41c00340000380107640b507410005800107600801e8404151000064403113841030a901c40b00280201c02868110300e0044003d4a0200318248040400514107070f800c5407003030150f030225a580d40040849410520403002400101e21685002207540e00142c00d1034a4010141d80c0c981c8640d00100c41e80039921900890f41c0140600314501038420010036a075144510003000c2d03540c070342c22241451422100380001c03c03194850010324a20f42c0d0124441d40c00a292a9514142420000c04400d042c28040c060001d9105450181000340790110440f2a502c0d82042d08507508010010020320500c00704000d000090703101c10405ca0541e17044540d80949403030044401c40c3c003034407450502a0f0b02d5103a110718041030f8034020818060405090302110510300902061180f580540c00b0440d07449100a0701c0d8204a102c0d035000342d64043d080321 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 261670791 1250 261669541 261669547
    0xf1006050f19020c0a091505131404081c1401090902012f120406051b01022b0c0801031707050712290603030906091309050c03010b010503040804120503 67
    0x2c5420303900a503180201005a0000c1080003450508401c0c0001501080307200380300e180c031104815290035000b44140c60248810b80001020a00d06510143c0e0001c0c440c000440542814242820b10307800c103041c240c8515a0051800c44049201d1088000c0148981407109081e807800c1045001442c0c1c1150690501100600d210f070907000805a107132048940309e48540009040794003851800b03030840b801403001801040306200440d0800d003a01d01c14100c0b2500301a015401c0742281d0701901515201c40c04c0c1802c04403003041551001c44609141d80c00908040180c0c0f0540c6101325000c40c0b0a2101512481c0313884960b8603244074030802008070768000c004441c0b80300e031b644140761000a403440c010b8440703141d0000c044004040740c9004c00301c02400d15403015540d061041c0000d03240e1145c044614850b110020f20b50405481c0c0b2614108a00c020310380c104503480180c10040e03216855403a1035840395203000b1031516990301541c2524001c0e1780000c0000e041504000d0340c4084403a0081003aa500c0c4014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 261672041 1250 261670791 261670807
    0xd080c030621010f0c0302032203210203011d04170f0f04080606010e01080f0c07031202070c0915180203040c08030d060311010807021005070905040c11060f1006050f 73
    0x1d0402c40001241000080c3c4820300c4030804c4101ca010701d401004050041050000101180c4400e242c002c070304070840c500d600b4840c5001d80b4101c540f03000c41c424508612014402403401540518102d648a06140c003215002c007407210740e071001c211401000c5a0806002e0b20340140c2210182c02c8240514a002e0b01d0b00440a00e1419550020b610180715076215104000721540c0c45107294410300000c0c2844d0101c0e0809481003200c07130400601d0080070741c1011440340207051140707058801180f0618021540c40046050200342c038813080c0074000396981000c10300c55280140500c0b182c211003d26140d0000ca01c1c2c00040200031303600180065030540341098004c9810041071000b40007486d01904001a02446e610300000d02d0002c04541c141403000c1402008000c075000b090704c2044000540000629030f6802c4001c2d03039000c142e0380103507801514142a21412a1300a01e540d107613005240101d420355034070801c4007102040c0894418411500641040103c60702402c040e1090b203a51000e218140340f10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 261673291 1250 261672041 261672079
    0x40c1b1b0308070c0914010e041505010b13060e01020c040b03010b0a1206050105010201020301030b041e080406110c03030307020a0201080c090414010302040506011403070c03050708040303200d080c0306 89
    0x11a030001d4890820009461041006112041c3c00806803010103004c101d03002c20000c0006c4a0511401e000c020000780080c0401542602420396520600340c02c01c4696140d03203100100e034200b0201411480e0000501244c020702610f0007a2110030140c2c000c0414084403020300006d4030b8909540b13a015900e41541c080581e035401e054802500c0c00307090022960205060000680303206a200c0d9041da441040184045815002010790080d0008440b0700849460703a450f0311000005480502650008507020540b150300c19400c24a40340b00c48203c40fa0b0002c0786c0d00305500ca12042d688800940c0c061030988005500030a00554002c89041000c1d080222100108003a500000c1e0f030108a440c1c444018821880c042c40303050380007a020702e0050f00c0f010350401204820b10001c1e01203010300c2121011842054812070807a08441d510071074130707501c490307883c81e01070084000ca83c18058000c1e00340038407600b07046000514605683c0c1d196507084079500c4a81c12014076a001604403a040692101a4124118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 261674541 1250 261673291 261673343
    0x80405062707080102071b05030d0e030307060615020c040e070501140c0106032f0a051c020d08040e07080403090902030a021b0c0406060c020a2d080105040b06040c1b 73
    0xc030200001da921b9220b807900e07590004240f003a55100c0c480181051000b1b403030016441c3d12500d414140940d00c26121800030740b4501401030010300007801d000012031401403201110440420940840d0900c2c40a0401c0009440804e903a00c201c0d5031100108001c950300c200c3c0200780d001065030025250280842e07125095038040e40080c0c44900000c160801d0300510044a20394441e501342d90382120403031080c006001c01d107007403044510800da00440003109400c504001c0c0d1130194002c000c1d03101c4a0140c6012080d80d04079110304074244c110f20b000281d85d5801031190510503940341d82d42170071a500b80f40e40403000b500f01400030002c140c1d0038806800e1440c0500b00054046070075000906e0029600004c1200341c40060b0840020001c48085c2180184ca07448021001d5a0b101c1c40b03080d03040c540102d071214554504070418000e0181e28007001072a100306501050103540154086541565014240804e1740c4031140b1036000074202c201c00d9400f071030803181030300c00603482108501c04008001d403050891780 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 261675791 1250 261674541 261674549
    0x6040506040b120703030215010b1e040b04060c050d0c05120a0306050a18050702030c0a0f0203030d1e0606020a0c12140304090b0306090c1f050c070303120c080405062707 75
    0x4c0e00c400424800e0640400c4696100d2080c0d00c400f41c00c0351704200300b40303505014194039600303a0201d14841c6c0381a000c401c001c1d18050080c0f001e006859595464000f0030070525113600390b076030740500740e0045031043c41195405405508071005180b000c1289090180c2544400341071030070159510301c089402c3c0c0c0d407582c41100a20300020300d040e44a005541c07440480c2d401501403070955004110b000314150380802e016003019004503505040c0c071107e002003415441851403200405103044001680020102064003c040140c1c4c1300704590790311707007800380c1c3d0700d45140748050268403219000300110700c104032880444038442c1c2d0512000da43c1c9600024035541098000300d0b070f05a22018110a075041c10409142e00151810081c40700441c400c010400e0b5408204000c012841c1600c4508042402402112a00f03081c0c80200d0700001c2d902d0800414501d10b00c00c00021150070110100e5a144c464440a401250000701034510f9071524055100032000800f18481c07000002185520300d24001d0150a00030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 261677041 1250 261675791 261675793
    0x60105060c070503191a07120c0311030c0a1101271a0f0a0b03031c050c070f060504021503040c0b0a020f0303010e0906070c0302060a090804050d050706030605030f030306040506040b12 81
    0x5c510900c0c150807046810a011880c003040e4034204200ea40c3d100c1804e11a4246207000058204000b44c41240030702581d41806881050002c148050300074003000812140c14650746101022000c0c0032110300340e8003100c0000c05650441c01d04803602d05179502c00040c0aa100d00030754103032202c1140ca0b441c000e4004491285070000841c04205035401c05004503506010f048001c0c40c03a01c4100505800041400803d0b08116036448000508490f840d03800c0385c1d120b40d04644a4124655107241810191000b110201d0140524002d10600035038041c0550740030301d90103049075034241c3c00c0003400551600981026000c502c958120603800c581c042c40114080c0048641e038542a1500c944c885160843c0505007400304180c440b01d20f40825808210700303070040c01c41c5001140e1069142850754050049801171944040502200c804011000514608580d22520140300c1540c0d5681016220f0081a159000c1d6030000c000040032882c10f54801076001b1b200910003d04a030405012a509d151064010340d42 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 261678291 1250 261677041 261677083
    0x16060509060109090818030705120f0d1e0c0501060f0308090f010f05120c07080a030b240d1808030f01031a01031113110f041a040305060105060c070503 67
    0x2403940a118035405040d2480c01131064484076543d000483c800c070300940e180805480c1162440d170384c00784501c0d0300900000384a181604001141991581110110050a4411014199a60750080050200d010711815041d40a8bc01e0100151032014418601716445d5584410210f80022180f591401560140c0703116a12600b941080c044c2060210b40900e043c4202c8840414400e5840001c42d010100e000005d0310b4941c5490b1500307002c41c003660304028556600811080c06043c0d040d07110203040c801c02c80c4c14601000c64040400c1681990300300484040e0710030031411080240c40c0d0014581d106c540c07010040c00c4925a101d920041d0000d4403001c50b0200d02d50010070078004118004c156000301c0e02c5031007590b549180d90f01051840e044403110700414652007030221500056100c0c1050120f83d4142e2a540c800507802d2498913801800344d544120003441c0342040d40d91170341d020342e010346e03030702c4001449075034240020081c4503080310344428098840e02c000460503450501000c28071400245034084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 261679541 1250 261678291 261678301
    0x51501030f05040c05150c03300108070918020a1d010b0906030f0403110109121101090c060e130606050702040e0307050a02130e011104172a0105160605 67
    0x10a0740d10020748298000c0c02c200900002c1024802c0032021111700b2240400e111079011240004c60180340100700c494000450701e0781c48802d8038280c02d040e60039288126400514007103048e4060950a00500c902075104040c01c1c13203602c01e0b03640800034000382c0e0403407030386011a1a8000307000b2000f07030340094a6407440c0c030704490341c803499101c1100d0142003010309140c1000400310115100d400300500840081d203030074000c181030500070035400c1e020070040c800921208240b403c0c0007420b58244000c00b0001141c21140440110041c401e0b07801141d4010608100c4030314101c4103c41d201d02e0110500da004089080d03171600301c83d075845820001d110984942d0384509641c0100412141c00c0e00d008010f40d00100242030000c1c2d408a01d00702401c0d4106c0f0b40c4074201d803c00c40008001c00c410350f60401c1540c0382c441c101002440c940050400c03110124440250060411041a00c076200d031940f0514100a0151403000c500c003102c407404025a040c5022410604001e42c10103210ba58400141c52960362401409 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 261680791 1250 261679541 261679547
    0x209010207051f0305160215190e0c12010e0a02040b010504050a06030b01140c0c011206081504120207050d0f05030708040e1602070f1202040b1002030a030f0c050a21051501 76
    0x5606c060030300040503500307001160280d210000c40014070080d441d980000351a00b040010001445920648204244410300400940d640c8801e01d07014030541c100300090380303460414000c0484003650080a400c0010f82582400017074a040c010389410300405020219590321075075502c0c00184415600030485103008030024090507070701d0300b1020840c4010000141042c0c0b0010300d0000442007031074140b998406065a100051203e038000f0000c9000705a0040603c0b00c0200c003880c00b860003203545c80d02650154505917580d618600c00d80390804807640190000c80e0014203814452030140c401c0c0c91800c240c6030707150200b0340d02507003095140c8030040041c0314451041a60442e41440f2a00041c280c1074100b85031400040002c0c45030410078032017039030507008545580c2c001c84a40d030070280203107020022102c006501d0340c100142c10400a4600500703c074400c03401d805500c0082003191106403822441a40c100d03804014620002132388000c01c29000003007001031160341c1c420700040031081190f086500c001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 261682041 1250 261680791 261680801
    0xb0a1704211d060307050307120e03300907060804080d05040309140301062108090a030803060111030f0306010503090f0a030f1d06040506160b0708042102100209010207051f03 77
    0x5074043c15050007000300040d0000200e0750400080d0425920602400d40d600c405810400038250b030038040820300c0130f800e14214259a00e40402e41429011140e46803860403818030007200c1e07070403655001e200d082151602034501290040c0c000c2c9000751400380d0460080b002e454042c1c40441c0000c0b0510750401c9642580364108101a0f0218001d10000b4500001c0b82608204592150104410910700b10b08020002c4101c52030030310702511481c0e0f8a507030383c18141d805410465400d07000c1030040030340014000001c41103600048101040c5811529488011911500b00806811541c40381e075420f95501c400c108900c000780e610942d292310708050a0903004082d04400b1360b030050700c19a410700d85c00e5580c0e038000035a02070300c05c15281661107034616030300c44420900203540608165500001c2c0030302c03c2d9000100c540301c4e034001c003400101c401454862504881440001000603080880c6e0000c44070001c2d0000c001c007020510440b1040303603e803c005190a880d0400315040c084411003400485d50f014040c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 261683291 1250 261682041 261682097
    0x70f05060703090303180e0c031005030708120f0d18060b04020a02060c09060417010c03200703031d0714090a051308030901110d0b0405010b0a170421 66
    0x141c146115940d01030861100c90200505010746401008101c3c19000c0286c401400d8205136004241000c408000c00c0d03600980d1203880c030384991280491310b4103000070110111a030300401030000c10314120a4007079540108016070034401c020880c0302c0c48002c0a01815003042e5013401500c0c07186180d803500c02d08485003c15198002e500500000c850725801003959940022481d009a80c0c0c0d0074080001030061259410401d00d00f0f00e00c201074210060154031040c0c5121268070100011a07041c2c131502945500000022802d0408201c501c000a100c0d401416182d000710f01880900f06031000c46070309000791a005114500b0714076201d0141c07890640c00e07140d003260741010100071906110b40003e514940a80c00545015800804a580d20384c003580106a2560000001501d03002006900300c040c10418040c075100360300f041d00206288660030304452035101191142c549940320603c00b06002ca01c018410b0340e20280d1164803100c02c01c024888070301000c106a445003000d00303d64580d8506990724443d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 261684541 1250 261683291 261683299
    0x15240d0501021306140702010e060903010c1e02070e06130e0106090c090e22030e190501110601050a090f060302180103021305010303020a0204050a2a0306291c0e070f05 74
    0x1481c1a02221010102d440341b54080c603040c3da000c08144040340f051307c14a07004a40540c85e03c10082c00403070b8000a02e0a0112003143c284000e003465000483c5c0e03c07031560045118045800d03010a4071440c12041e480150300c0d06120115006003100d600b075086480c0d87d40141d00c51611401c43c12a2075600c84070342d1010340780120400d903160401e00000400440c4640444007a40c540112003c14540146202030a412004040b001c824000003030551188010f072180e82d020a52103483d490748001c001c20a58180c81019002c45010303450511148081e01041001440c061703519000400543c8600098004625100800d034a680d4036620510500c1c00c0a009009103a41c81c4c14010300009078041103000341c1940445000c12145c454584002c000c0091001d00754040080c80c034000c103404001010054170440c40e17241004025554096800d0324601c41049070309250086400100d40c1c6190000382c064214282091314080748020079641c215400301c0c011303090584c0110010002e403046600c164000e098262 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 261685791 1250 261684541 261684557
    0x608070e031501060503040f06020711040e0d1e050c1209011103030f24090f060301150e0a020309010b130204030506012112141201140315240d0501021306 68
    0x480d40d090300704180603803800c05c071002003c01d0500880c8a44445500d401c403a04640c0e0328002e01e026904420000c02c500d001e1820800d1440304004045000c0c50354a00645802c0c143c0d01d03080030080c0c01150080422014000c04ac000200b10172801c1114800390700400000c1684e610a681c005098441c120000d00308682c000c000300301001e01c2070300340d843e0444400001408089901304221603000d41415119800203205010041010001030364640142029402000744804164902c6682800d500a81c40a00800000700d1086402a401907502001d146c00004281d200c00d00001d46100411246800c06e5401041c14400c0c80320500646005042511413001e428504980102c1c000c4d681920203040c80c40f5001e541a0841d0080009800081c8403a48041c2c0d1200e4002904810000a0060000f00c004508110003181800101e032003d895642012240750303600c1561440ba0407408002e080042d040c004640603050300c402525203100c3c2d200c2c0c400507072a601c8048511903048001c2c2d000b641048040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 261687041 1250 261685791 261685813
    0x20f040f050f03030a051b0c1f0816020a022709030408101e020a03060b0a090306140915040311190b13030e0d0501060f0e190c09060804020315010608070e03 69
    0x2000c00c84d2221501b0300203489400c600c2c0031407581048e007038016041d04200c0080c140710404883c8000000c404020340c03078032222920762070700c2000f940900ca6402000740c0c1c00181004098540810090070402420b000080c4045841e811200340351400e0310a4107180d8004a014804500103100c42d841c2c1c5100380b481004409907568a462452042d1611040b4880d40020a8908580b00341c11000c041d00303070b170750f111681c0e0b507100c0c2c500424081c100c0c4003d80e0b41a1a004600f9100743c00500d065014100350401410300c800854144010030700c0103481107050051107403c2450001007803010607580c8680d000440e079101c200307051505400c5c0d402810420014002e116500c0001d800c20300a000f4000180c52110f0101e00c24500f00740140110340252074144e03100c0d54005255404004c15600c500107800c0703400c000c420441c62020a4401c0702551002041c1c80d10420f0007424400c508103580580020120f0b505002d0600004003c2c1400b078102100060b44c4100b0406199041000b1104161050340185458511 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 261688291 1250 261687041 261687047
    0xf0d02070c0612140633130e0405070306050c0d0e010b040e060601200c091503121206101205040309032603010b0f0c0f060712060e07030906020f040f050f03030a 71
    0x4000c050601c2001202d9180e1840c00040709000441d80c803140840c6421b14080307a952035542c00c140401d1219800c0b141d00400e0110304605120b010f198450003e00701300b402c640d81e000280100501811465006000e4141180319602540d11000c0450000080c01200c031030900003511402d00442e0010340c000c83c14001c00c0c1c1d074000c8011641c080e81c0340c3c00c4152841e80c107141d1404c0c0045001c07450740c4801d1400c00e1101c100d0a0408800700858206c046801a540349a000c030418001d80e01c0e00302030380c402040020014204020f15a44070300c220f2406032250743c4200b2066048500945040c0e0004503040703014400c0200c04030301606644080c00400d45600746814402c081480140a00d482401c0040f8a622625a8850595040e42401c1d015903007558500c07111180e960408440f03400014502e02195059015248114001c0e98003500000c10599560502070f0050b01150f1000c40f85241e00308040b00d0a8003102c00030340301404440362203400452a117010402c0d000e400c030100c0c6101fa0402c04c81c4004880d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 261689541 1250 261688291 261688331
    0x2307020103090203031e0d1d060412020a02150702130b0f04090215040b070530070507030c0801020403030806040c170c040306060906170a0213020f0d02070c0612 71
    0x5424a000300c0c04050038804a411802101c1101300782e61101c541c1846d4101c1c8080103050501d00d160020090200c051030b000c0c0d5405548592144150000380c003080103c2c0b240c0c0c14401841c4c402e4011504420303003036808280c8402420008403140d803000300e142c008500d0306285607159038902000520140a192000568088400080d14400d80d030b110070341000c540381d42e140da03003c1543c80c0d084545c86a82e10b81e2074401c00d42c00120101d85500030041c24025501d0a1a03030548403007080a0080390401c0b6140d40d12003107908c2810207842610400324000001403c0c83c2c00701002c2d103c91400582c4492440c540901214006040c451095040c0002c414001e68407004c0703003010070340140322a41641c90b0a0480c15003485281c0000d00114205940850f000e00a40c110f04e0072600400f00c140c5021542841450700c490744404003d50105e100040142119039035000b0300348892149158626100603240f104040341d100ba1000c68400c4855001004107d40010f10b106240d0b0f2001400d005070b1000c849462074441d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 261690647 1106 261689541 261689543
    0xb031513050903041206140108010c11070e0a150e090604030801060e1818010603050a02030c0a0e0103060c050c1005180307030503240303040306020a2307 68
    0x4250361203501c0c03084039038001a42c10300341440d00c4805c41403483d1009540c00f07621400030b00d1561200802c418000c03da8603000050041d1900e6001d0700c0da01c40440515050380200000308511400e02030107039440000704c1000641030845070b401c1850410b0a4010b00440c804200c00c10000e1140003545500440c0039841e5102d503070780c0c0e9031400c41c0c80001881109400014020b40d8071802e29200b440f0310740190710b001d601540c0c554050586402c4411660050b80c4035070103181100d05605091210440604098804c03401c020b0a05403000d40080c1e0603c0018032543c1d45507036110055104030107899042207c00309860382042c208507444003034142600d101840d003600b008001c0340904004212081c0030b43c107854040c1540e54440080f80d507404841d030445454440d606500400d0781c0c00380010005103200391001030315992140ea00420300c00825007110100301c010b084185840900005891541d = true := by decide +kernel

theorem cover : BRFrame.Cov 261510791 261690647 := by
  have h0 := BRFrame.cov_init 261510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 261510791 ≤ n) (h2 : n < 261690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
