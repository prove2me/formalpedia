-- Prove2me | solution 1 for DiazModulus.boxHilb_hilbert_side
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:09:21.090253+00:00
-- url     : https://prove2.me/submissions/d560f242-bf11-4c5c-80cc-f44830c31aee

import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_boxHilb_le_of_height
import Theorems.Thm_DiazModulus_boxHilb_mono
import Theorems.Thm_DiazModulus_le_of_forall_mul_pow_le

open Complex ComplexConjugate

/-! # The Hilbert side of Th. 8.1★, abstract

Let `I = (ps₀)`, `I' = I + (V)` and `j = max_b C_b`. Since every `D_b ≥ 1`, the shifted box
`u·D + C` lies in `w·D` with `w = u + j`, so by monotonicity (`boxHilb_mono`) the lower bound
reads `λ u^{n−r} ≤ h_{I'}(w·D)`. The regular chain (`boxHilb_le_of_height`, Th. 8.8★) at `w`
and the upper bound give `2^{r(r−1)/2} w^r h_{I'}(w·D) ≤ h_I(2^r w·D) ≤ κ (2^r w + 1)^n`.
For `u ≥ 1`, `u^n ≤ u^{n−r} w^r` for every `r` (if `r > n` then `u^{n−r} = 1` and
`u^n ≤ u^r`), so no `r ≤ n` is needed. Since `2^r w + 1 ≤ 2^r (w + 1)`, this gives
`λ 2^{r(r−1)/2} u^n ≤ κ 2^{rn} (u + (j + 1))^n` for all `u ≥ 1`, and the leading-coefficient
extraction `le_of_forall_mul_pow_le` concludes. -/

namespace C11_A3
open DiazModulus

/-- `u^n ≤ u^{n−r} w^r` when `1 ≤ u ≤ w`, for every `r`. -/
theorem pow_le_pow_sub_mul (u w n r : ℕ) (hu : 1 ≤ u) (hw : u ≤ w) :
    u ^ n ≤ u ^ (n - r) * w ^ r := by
  rcases le_or_gt r n with h | h
  · calc u ^ n = u ^ (n - r) * u ^ r := by rw [← pow_add, Nat.sub_add_cancel h]
      _ ≤ u ^ (n - r) * w ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw r)
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, one_mul]
    exact (Nat.pow_le_pow_right hu h.le).trans (Nat.pow_le_pow_left hw r)

/-- `(2^r w + 1)^n ≤ 2^{rn} (w + 1)^n`. -/
theorem shift_pow_le (r w n : ℕ) : (2 ^ r * w + 1) ^ n ≤ 2 ^ (r * n) * (w + 1) ^ n := by
  have h1 : 2 ^ r * w + 1 ≤ 2 ^ r * (w + 1) := by
    have := Nat.one_le_two_pow (n := r)
    rw [mul_add, mul_one]; omega
  calc (2 ^ r * w + 1) ^ n ≤ (2 ^ r * (w + 1)) ^ n := Nat.pow_le_pow_left h1 n
    _ = 2 ^ (r * n) * (w + 1) ^ n := by rw [mul_pow, pow_mul]

end C11_A3

open DiazModulus C11_A3 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] [Fintype B] [IsNoetherianRing S] [Infinite K]
    (F : (B → ℕ) → Submodule K S) (hFmono : Monotone F)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ))
    (hU : UnmixedHeight S)
    (ps₀ : List S) (hps₀ : RingTheory.Sequence.IsWeaklyRegular S ps₀) (D : B → ℕ) (hD : ∀ b, 1 ≤ D b)
    (V : Submodule K S) (hV : V ≤ F D) (r n : ℕ)
    (hH : ∀ p : Ideal S, p.IsPrime → Ideal.ofList ps₀ ⊔ Ideal.span (V : Set S) ≤ p →
      ((ps₀.length + r : ℕ) : ℕ∞) ≤ p.height)
    (κ : ℕ) (hup : ∀ v : ℕ, boxHilb F (Ideal.ofList ps₀) (v • D) ≤ κ * (v + 1) ^ n)
    (lam : ℕ) (C : B → ℕ)
    (hlow : ∀ u : ℕ, 1 ≤ u → lam * u ^ (n - r) ≤ boxHilb F (Ideal.ofList ps₀ ⊔ Ideal.span (V : Set S)) (u • D + C)) :
    lam * 2 ^ (r * (r - 1) / 2) ≤ κ * 2 ^ (r * n) := by
  set j := Finset.univ.sup C with hj
  refine DiazModulus.le_of_forall_mul_pow_le _ _ (j + 1) n fun u hu => ?_
  set w := u + j with hw
  set I' := Ideal.ofList ps₀ ⊔ Ideal.span (V : Set S)
  have hbox : u • D + C ≤ w • D := by
    intro b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw, add_mul]
    have h1 : C b ≤ j := Finset.le_sup (f := C) (Finset.mem_univ b)
    have h2 : j ≤ j * D b := Nat.le_mul_of_pos_right j (hD b)
    omega
  have hlow' : lam * u ^ (n - r) ≤ boxHilb F I' (w • D) :=
    (hlow u hu).trans (DiazModulus.boxHilb_mono F hFmono hFfin I' hbox)
  have hchain := DiazModulus.boxHilb_le_of_height F hFmono hFmul hFfin hU ps₀ hps₀ D V hV r hH w
  have hup' := hup (2 ^ r * w)
  have hpow := pow_le_pow_sub_mul u w n r hu (by omega)
  calc lam * 2 ^ (r * (r - 1) / 2) * u ^ n
      ≤ lam * 2 ^ (r * (r - 1) / 2) * (u ^ (n - r) * w ^ r) := Nat.mul_le_mul_left _ hpow
    _ = 2 ^ (r * (r - 1) / 2) * w ^ r * (lam * u ^ (n - r)) := by ring
    _ ≤ 2 ^ (r * (r - 1) / 2) * w ^ r * boxHilb F I' (w • D) := Nat.mul_le_mul_left _ hlow'
    _ ≤ κ * (2 ^ r * w + 1) ^ n := hchain.trans hup'
    _ ≤ κ * (2 ^ (r * n) * (w + 1) ^ n) := Nat.mul_le_mul_left _ (shift_pow_le r w n)
    _ = κ * 2 ^ (r * n) * (u + (j + 1)) ^ n := by rw [hw]; ring
