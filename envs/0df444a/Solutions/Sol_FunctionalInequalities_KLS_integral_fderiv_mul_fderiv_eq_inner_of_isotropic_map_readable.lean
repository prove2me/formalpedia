-- Prove2me | solution 1 for FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:23.027823+00:00
-- url     : https://prove2.me/submissions/dc22d799-178c-450f-a7cf-fbecb861a427

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Gradient second moments of an isotropic pushforward** (Letwin Lemma 2.3, step 2): if `(∇φ)_* ν` is isotropic then
`∫ (∂_u φ)(∂_v φ) dν = ⟪u, v⟫`. -/
theorem solution
    (ν : ProbabilityMeasure E) {φ : E → ℝ} (hφ : Measurable (gradient φ))
    (hiso : FunctionalInequalities.KLS.Isotropic (ν.map hφ.aemeasurable)) (u v : E) :
    ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) = ⟪u, v⟫ := by
    have hderiv (x w : E) :
        fderiv ℝ φ x w = ⟪w, gradient φ x⟫ := by
      rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply, real_inner_comm]

    have hmeas :
        AEStronglyMeasurable
          (fun y : E => ⟪u, y⟫ * ⟪v, y⟫)
          ((ν : Measure E).map (gradient φ)) := by
      exact
        ((continuous_const.inner continuous_id).mul
          (continuous_const.inner continuous_id)).aestronglyMeasurable

    calc
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) =
          ∫ x, ⟪u, gradient φ x⟫ * ⟪v, gradient φ x⟫ ∂(ν : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hderiv x u, hderiv x v]
      _ = ∫ y, ⟪u, y⟫ * ⟪v, y⟫
            ∂((ν : Measure E).map (gradient φ)) := by
        exact (integral_map hφ.aemeasurable hmeas).symm
      _ = ⟪u, v⟫ := by
        have h := hiso.integral_inner_mul_inner u v
        simp only [ProbabilityMeasure.toMeasure_map] at h
        exact h
