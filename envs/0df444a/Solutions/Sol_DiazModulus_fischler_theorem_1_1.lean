-- Prove2me | solution 1 for DiazModulus.fischler_theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:22:41.376537+00:00
-- url     : https://prove2.me/submissions/af0e358d-0171-45f8-8340-35d1655713b3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fischler_linear_pow_prod_mem
import Theorems.Thm_DiazModulus_fischler_power_span_finrank
import Theorems.Thm_DiazModulus_fischler_rational_hull

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 1.1

Let `P = Λᵏ` with `Λ = Σᵢ λᵢXᵢ`, `k ≥ 3`, and every coefficient of `P` in `ℒ̃`. Then every product
`λ_{I(0)}⋯λ_{I(k−1)}` lies in `ℒ̃` (the coefficients of `Λᵏ` are positive integer multiples of these products,
read off by differentiation), so the `Q̄`-span of `λ₁, …, λ_m` has dimension at most `1`, as `k ≥ 3`. Write
`λ = Σₐ cₐwₐ` with `Q̄`-free `cₐ` and `Q̄`-free algebraic vectors `wₐ`, the number of terms being that dimension.
If it is `0`, then `λ = 0`, so `P = 0 = 0·0ᵏ`. If it is `1`, then `λ = c₀w₀` with `w₀` algebraic and non-zero:
choosing `j` with `w₀ⱼ ≠ 0`, `λⱼᵏ = c₀ᵏw₀ⱼᵏ ∈ ℒ̃`, and dividing by the non-zero algebraic number `w₀ⱼᵏ` gives
`a = c₀ᵏ ∈ ℒ̃`. Then `Λ = c₀·φ` with `φ = Σᵢ w₀ᵢXᵢ`, and `P = aφᵏ`. -/

namespace RC9_F4
open DiazModulus

/-- If `v = c • w` with `w` algebraic and non-zero and every `k`-fold product of the `v i` is in `ℒ̃`,
then `cᵏ ∈ ℒ̃`. -/
theorem pow_mem {m k : ℕ} (v : Fin m → ℂ) (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde)
    (c : ℂ) (w : Fin m → ℂ) (hwQ : ∀ i, w i ∈ Qbar) (hw0 : w ≠ 0) (hvw : ∀ i, v i = c * w i) :
    c ^ k ∈ LogAlgTilde := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  have hq0 : (⟨w j ^ k, Qbar.pow_mem (hwQ j) k⟩ : ↥Qbar) ≠ 0 := by
    intro h; exact hj (pow_eq_zero_iff'.1 (congrArg Subtype.val h)).1
  rw [← Submodule.smul_mem_iff LogAlgTilde hq0, Subfield.smul_def, smul_eq_mul]
  have := hv (fun _ => j)
  rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hvw, mul_pow, mul_comm] at this

end RC9_F4

open DiazModulus MvPolynomial in
theorem solution {m k : ℕ} (hk : 3 ≤ k) (P : MvPolynomial (Fin m) ℂ)
    (hP : ∀ s, P.coeff s ∈ LogAlgTilde) (Λ : Fin m → ℂ)
    (hPΛ : P = (∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ k) :
    ∃ φ : Fin m → ℂ, (∀ i, φ i ∈ Qbar) ∧ ∃ a ∈ LogAlgTilde,
      P = MvPolynomial.C a * (∑ i, MvPolynomial.C (φ i) * MvPolynomial.X i) ^ k := by
  subst hPΛ
  have hI := DiazModulus.fischler_linear_pow_prod_mem Λ hP
  have hn := (DiazModulus.fischler_power_span_finrank (by omega) Λ hI).2 hk
  obtain ⟨n, c, w, hn', -, hw, hwQ, hvw, -⟩ := DiazModulus.fischler_rational_hull Λ
  rw [← hn'] at hn
  interval_cases n
  · refine ⟨0, fun _ => zero_mem _, 0, zero_mem _, ?_⟩
    have hΛ0 : Λ = 0 := by simpa using hvw
    simp [hΛ0, zero_pow (show k ≠ 0 by omega)]
  · have hv1 : ∀ i, Λ i = c 0 * w 0 i := fun i => by simpa using congr_fun hvw i
    refine ⟨w 0, hwQ 0, c 0 ^ k, RC9_F4.pow_mem Λ hI (c 0) (w 0) (hwQ 0) (hw.ne_zero 0) hv1, ?_⟩
    have hL : (∑ i, C (Λ i) * X i : MvPolynomial (Fin m) ℂ) = C (c 0) * ∑ i, C (w 0 i) * X i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hv1, C_mul, mul_assoc]
    rw [hL, mul_pow, C_pow]
