-- Prove2me | solution 1 for FunctionalInequalities.KLS.RegularPotential.isotropic_comp_affine_of_whitening_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:28.958413+00:00
-- url     : https://prove2.me/submissions/9f394b81-aba0-4e92-b94a-b98f19092058

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isotropic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
import Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_memLp_id_two_readable
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_law_comp_affine_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (c : V)
variable [CompleteSpace V]
/-- Translation does not change the covariance operator. -/
theorem FunctionalInequalities.Covariance.operator_translateLaw :
    Covariance.operator (Probability.translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [Probability.coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]
end Translation
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : MeasureTheory.ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
omit [SecondCountableTopology V₁] in
/-- The covariance operator of the image law. -/
theorem FunctionalInequalities.Covariance.operator_mapContinuousLinearEquiv :
    Covariance.operator (Probability.mapContinuousLinearEquiv ν T : Measure V₂) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator (ν : Measure V₁))).comp
        (T : V₁ →L[ℝ] V₂).adjoint :=
  Covariance.operator_map_continuousLinearEquiv_readable (ν : Measure V₁) T
omit [SecondCountableTopology V₁] in
/-- The barycenter of the image law is the image of the barycenter. -/
theorem FunctionalInequalities.Probability.integral_id_mapContinuousLinearEquiv (hint : Integrable id (ν : Measure V₁)) :
    ∫ y, y ∂(Probability.mapContinuousLinearEquiv ν T : Measure V₂) = T (∫ x, x ∂(ν : Measure V₁)) := by
  rw [Probability.coe_mapContinuousLinearEquiv, integral_map T.continuous.measurable.aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V₁ ↦ x) (ν : Measure V₁) := hint
  exact (T : V₁ →L[ℝ] V₂).integral_comp_comm hint'
omit [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] in
/-- The image law keeps a finite second moment. -/
theorem FunctionalInequalities.Probability.memLp_id_two_mapContinuousLinearEquiv (h : MemLp id 2 (ν : Measure V₁)) :
    MemLp id 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) := by
  rw [Probability.coe_mapContinuousLinearEquiv, memLp_map_measure_iff aestronglyMeasurable_id
    T.continuous.measurable.aemeasurable]
  exact (T : V₁ →L[ℝ] V₂).comp_memLp' h
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
end ContinuousLinearEquiv
end
end
end

section
noncomputable section
open MeasureTheory Set
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_readable hνW hW hconv)
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
variable {V : E → ℝ} {a b : ℝ}
theorem FunctionalInequalities.KLS.RegularPotential.logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge_readable hW hV.pos.le hV.lower)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end

section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section RegularAffineLaws
variable {V : E → ℝ} {a b : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b)
include hV in
/-- The law of `V ∘ (L · + c)` as a translation followed by the continuous linear equivalence `L⁻¹`. -/
theorem FunctionalInequalities.KLS.RegularPotential.law_comp_affine_eq_map
    (L : E ≃L[ℝ] E) (c : E) :
    (RegularPotential.comp_affine hV L c).law =
      Probability.mapContinuousLinearEquiv (Probability.translateLaw hV.law (-c)) L.symm := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [RegularPotential.law_comp_affine_readable hV L c, Probability.coe_mapContinuousLinearEquiv, Probability.coe_translateLaw,
    Measure.map_map L.symm.continuous.measurable (by fun_prop)]
  congr 1
  funext y
  change L.symm (y - c) = L.symm (-c + y)
  congr 1
  abel
end RegularAffineLaws
end
end
end

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : E → ℝ} {a b : ℝ}
/-- A regular law has a finite second moment. -/
theorem FunctionalInequalities.KLS.RegularPotential.memLp_id_two (hV : KLS.RegularPotential V a b) : MemLp id 2 (hV.law : Measure E) :=
  hV.logConcave_law.memLp_id_two_readable
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.KLS.RegularPotential.memLp_two_translate (μ : ProbabilityMeasure E) (c : E)
    (h2 : MemLp id 2 (μ : Measure E)) :
    MemLp id 2 (Probability.translateLaw μ c : Measure E) := by
  rw [Probability.coe_translateLaw]
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr ((memLp_const c).add h2)
/-- Centering and whitening by a self-adjoint `W` with `⟪Cov (W u), W v⟫ = ⟪u, v⟫` makes the affine
regular potential `V (W⁻¹ · + mean)` isotropic. -/
theorem solution (hV : FunctionalInequalities.KLS.RegularPotential V a b)
    (W : E ≃L[ℝ] E) (hWadj : (W : E →L[ℝ] E).adjoint = W)
    (hW : ∀ u v, inner ℝ (FunctionalInequalities.Covariance.operator (hV.law : Measure E) (W u)) (W v) = inner ℝ u v) :
    FunctionalInequalities.KLS.Isotropic (FunctionalInequalities.KLS.RegularPotential.comp_affine hV W.symm
      (∫ x, x ∂(hV.law : Measure E))).law := by
  let c : E := ∫ x, x ∂(hV.law : Measure E)
  let μc := FunctionalInequalities.Probability.translateLaw hV.law (-c)
  let μt := FunctionalInequalities.Probability.mapContinuousLinearEquiv μc W
  have hc2 : MemLp id 2 (μc : Measure E) := FunctionalInequalities.KLS.RegularPotential.memLp_two_translate _ _ (FunctionalInequalities.KLS.RegularPotential.memLp_id_two hV)
  have ht2 : MemLp id 2 (μt : Measure E) := FunctionalInequalities.Probability.memLp_id_two_mapContinuousLinearEquiv μc W hc2
  have hmean_c : ∫ x, x ∂(μc : Measure E) = 0 :=
    FunctionalInequalities.Probability.integral_id_translateLaw_neg_integral hV.law ((FunctionalInequalities.KLS.RegularPotential.memLp_id_two hV).integrable one_le_two)
  have hmean_t : ∫ y, y ∂(μt : Measure E) = 0 := by
    rw [FunctionalInequalities.Probability.integral_id_mapContinuousLinearEquiv μc W (hc2.integrable one_le_two), hmean_c, map_zero]
  have hcov_t : FunctionalInequalities.Covariance.operator (μt : Measure E) = ContinuousLinearMap.id ℝ E := by
    rw [FunctionalInequalities.Covariance.operator_mapContinuousLinearEquiv, FunctionalInequalities.Covariance.operator_translateLaw, hWadj]
    refine ContinuousLinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [← hWadj, ContinuousLinearMap.adjoint_inner_left, hWadj]
    exact hW u v
  rw [FunctionalInequalities.KLS.RegularPotential.law_comp_affine_eq_map hV W.symm c, ContinuousLinearEquiv.symm_symm]
  exact ⟨ht2, hmean_t, hcov_t⟩
