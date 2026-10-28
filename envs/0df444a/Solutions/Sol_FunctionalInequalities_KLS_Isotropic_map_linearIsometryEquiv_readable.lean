-- Prove2me | solution 1 for FunctionalInequalities.KLS.Isotropic.map_linearIsometryEquiv_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:47.521244+00:00
-- url     : https://prove2.me/submissions/5585c26a-4d8b-43b0-b759-ef1a902aec16

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
/-- **Isotropy from moments**: finite second moment, mean zero and `∫ ⟪u, x⟫⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.isotropic_of_moments
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) (h2 : MemLp id 2 (ν : Measure E))
    (h0 : ∫ x, x ∂(ν : Measure E) = 0)
    (hcov : ∀ u v : E, ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E) = ⟪u, v⟫) :
    Isotropic ν := by
    refine ⟨h2, h0, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right (𝕜 := ℝ)
    intro v
    rw [Covariance.operator_inner]
    rw [ProbabilityTheory.covarianceBilin_apply h2]
    simpa [h0] using hcov u v
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
section LinearIsometry
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- **Isotropy along a linear isometry**.
The `MemLp` step uses `ContinuousLinearMap.comp_memLp'`. -/
theorem solution {ν : ProbabilityMeasure E}
    (hν : FunctionalInequalities.KLS.Isotropic ν) (φ : E ≃ₗᵢ[ℝ] F) :
    FunctionalInequalities.KLS.Isotropic (ν.map φ.continuous.measurable.aemeasurable) := by
    let μ : Measure F := Measure.map φ (ν : Measure E)
    have hmem : MemLp id 2 μ := by
      change MemLp id 2 (Measure.map φ (ν : Measure E))
      apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
        φ.continuous.measurable.aemeasurable).2
      exact φ.toContinuousLinearMap.comp_memLp' hν.memLp_two
    have hmean : (∫ x, x ∂μ) = 0 := by
      change (∫ x, id x ∂Measure.map φ (ν : Measure E)) = 0
      rw [integral_map φ.continuous.measurable.aemeasurable
        continuous_id.aestronglyMeasurable]
      have hint : Integrable id (ν : Measure E) :=
        hν.memLp_two.integrable (by norm_num)
      calc
        (∫ x, id (φ x) ∂(ν : Measure E)) =
            ∫ x, φ (id x) ∂(ν : Measure E) := by rfl
        _ = φ (∫ x, id x ∂(ν : Measure E)) :=
          φ.toContinuousLinearMap.integral_comp_comm hint
        _ = 0 := by simp [hν.mean_zero]
    refine FunctionalInequalities.KLS.isotropic_of_moments
      (ν.map φ.continuous.measurable.aemeasurable) hmem hmean ?_
    intro u v
    let g : F → ℝ := fun x => ⟪u, x⟫ * ⟪v, x⟫
    have hg : AEStronglyMeasurable g μ := by
      exact
        ((continuous_const.inner continuous_id).mul
          (continuous_const.inner continuous_id)).aestronglyMeasurable
    change (∫ x, g x ∂Measure.map φ (ν : Measure E)) = ⟪u, v⟫
    rw [integral_map φ.continuous.measurable.aemeasurable hg]
    have hu : ∀ x : E, ⟪u, φ x⟫ = ⟪φ.symm u, x⟫ := by
      intro x
      simpa using φ.inner_map_map (φ.symm u) x
    have hv : ∀ x : E, ⟪v, φ x⟫ = ⟪φ.symm v, x⟫ := by
      intro x
      simpa using φ.inner_map_map (φ.symm v) x
    calc
      (∫ x, g (φ x) ∂(ν : Measure E)) =
          ∫ x, ⟪φ.symm u, x⟫ * ⟪φ.symm v, x⟫ ∂(ν : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, hu, hv]
      _ = ⟪φ.symm u, φ.symm v⟫ :=
        hν.integral_inner_mul_inner (φ.symm u) (φ.symm v)
      _ = ⟪u, v⟫ := by
        simpa only [φ.apply_symm_apply] using
          (φ.inner_map_map (φ.symm u) (φ.symm v)).symm
