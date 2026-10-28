-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.gradient_convolution_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:38.879511+00:00
-- url     : https://prove2.me/submissions/a0ac4c26-e10c-424f-bceb-4488f7c07698

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
section Derivative
variable (φ : ContDiffBump (0 : V))
/-- The mollifier commutes with the gradient on smooth compactly supported functions:
`∇(ρ ⋆ g) = ρ ⋆ ∇g`. -/
theorem solution {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x := by
  have hρ : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  have hd := HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hgc hρ
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)) x
  have hg1 : Continuous (fderiv ℝ g) := (hg.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_fderiv one_ne_zero
  refine ext_inner_right ℝ fun v => ?_
  have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t))
      (gradient g (x - t))) m :=
    HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed
      ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (hg.of_le (WithTop.coe_le_coe.mpr le_top))).locallyIntegrable) x
  have hL : ⟪gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x, v⟫ =
      ∫ t, φ.normed m t * fderiv ℝ g (x - t) v ∂m := by
    rw [gradient, toDual_symm_apply, hd.fderiv, convolution_precompR_apply _ hρ (hgc.fderiv ℝ) hg1,
      convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hR : ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x, v⟫ =
      ∫ t, φ.normed m t * fderiv ℝ g (x - t) v ∂m := by
    rw [convolution_def, real_inner_comm, ← integral_inner hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_right]
    rw [real_inner_comm _ v, inner_gradient_left]
  rw [hL, hR]
