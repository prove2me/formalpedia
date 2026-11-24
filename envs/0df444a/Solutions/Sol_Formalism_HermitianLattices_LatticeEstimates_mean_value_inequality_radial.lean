-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.mean_value_inequality_radial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.933854+00:00
-- url     : https://prove2.me/submissions/272d3579-fe59-4a27-a246-4c0b3ad0dd86

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution : MeanValueInequalityRadial := by
  intro E _ _ _ _ _ μ _ F hF hinv hint
  let f : ℝ → E → ℝ := fun θ w => ‖F (Complex.exp (θ * Complex.I) • w)‖ ^ 2
  have hFc : Continuous F := hF.continuous
  have hcont : Continuous (Function.uncurry f) := by
    have : Function.uncurry f = fun p : ℝ × E => ‖F (Complex.exp (p.1 * Complex.I) • p.2)‖ ^ 2 := rfl
    rw [this]
    fun_prop
  have h2pi : (0:ℝ) ≤ 2 * π := by positivity
  have hpt : ∀ w : E, ‖F 0‖ ^ 2 ≤ (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2 * π, f θ w) := by
    intro w
    let G : ℂ → ℂ := fun ζ => (F (ζ • w)) ^ 2
    have hG : Differentiable ℂ G := by
      have h1 : Differentiable ℂ (fun ζ : ℂ => ζ • w) := by fun_prop
      exact (hF.comp h1).pow 2
    have hmv : Real.circleAverage G 0 1 = G 0 := (hG.diffContOnCl).circleAverage
    have hG0 : ‖G 0‖ = ‖F 0‖ ^ 2 := by simp [G]
    rw [← hG0, ← hmv, Real.circleAverage_def, norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    refine (intervalIntegral.norm_integral_le_integral_norm h2pi).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [G, f, circleMap]
  have hmeas : ∀ θ : ℝ, Measurable (fun w : E => Complex.exp (θ * Complex.I) • w) := fun θ =>
    (continuous_const_smul _).measurable
  have hsm : AEStronglyMeasurable (fun w => ‖F w‖ ^ 2) μ := hint.1
  have hslice_int : ∀ θ, Integrable (f θ) μ := by
    intro θ
    have h1 := hint
    rw [← hinv θ] at h1
    exact (integrable_map_measure (by rw [hinv θ]; exact hsm) (hmeas θ).aemeasurable).mp h1
  have hslice : ∀ θ, ∫ w, f θ w ∂μ = ∫ w, ‖F w‖ ^ 2 ∂μ := by
    intro θ
    conv_rhs => rw [← hinv θ]
    rw [integral_map (hmeas θ).aemeasurable (by rw [hinv θ]; exact hsm)]
  have hprod : Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc 0 (2 * π))).prod μ) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun θ => hslice_int θ, ?_⟩
    have h1 : (fun θ => ∫ w, ‖Function.uncurry f (θ, w)‖ ∂μ) = fun _ => ∫ w, ‖F w‖ ^ 2 ∂μ := by
      funext θ
      rw [← hslice θ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp [f]
    rw [h1, Set.uIoc_of_le h2pi]
    exact integrable_const _
  have hswap := intervalIntegral_integral_swap hprod
  have hI : Integrable (fun w => ∫ θ in (0:ℝ)..2 * π, f θ w) μ := by
    have h := hprod.integral_prod_right
    simpa [intervalIntegral.integral_of_le h2pi, Set.uIoc_of_le h2pi, Function.uncurry] using h
  calc ‖F 0‖ ^ 2 = ∫ _w, ‖F 0‖ ^ 2 ∂μ := by simp
    _ ≤ ∫ w, (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2 * π, f θ w) ∂μ :=
        integral_mono (integrable_const _) (hI.const_mul _) hpt
    _ = (2 * π)⁻¹ * ∫ w, (∫ θ in (0:ℝ)..2 * π, f θ w) ∂μ := integral_const_mul _ _
    _ = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, (∫ w, f θ w ∂μ) := by rw [hswap]
    _ = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, (∫ w, ‖F w‖ ^ 2 ∂μ) := by simp_rw [hslice]
    _ = ∫ w, ‖F w‖ ^ 2 ∂μ := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by positivity), one_mul]
end Formalism.HermitianLattices.LatticeEstimates
