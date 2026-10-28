-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:38.627632+00:00
-- url     : https://prove2.me/submissions/faab6d39-2bdb-4570-9b6c-b8a363b9f24e

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_laplace_readable

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- `γ_s` has a finite second moment. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_readable (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.hasFDerivAt_exp_norm_sq_div {s : ℝ} (hs : 0 < s) (z : E) :
    HasFDerivAt (fun w : E => Real.exp (‖w‖ ^ 2 / (4 * s)))
      ((Real.exp (‖z‖ ^ 2 / (4 * s)) / (2 * s)) • innerSL ℝ z) z := by
  have hn : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hq : HasFDerivAt (fun w : E => ‖w‖ ^ 2 / (4 * s))
      ((4 * s)⁻¹ • (2 • innerSL ℝ z)) z := by
    convert! hn.const_mul (4 * s)⁻¹ using 1
    funext w
    simp only [div_eq_mul_inv]
    ring
  have h := hq.exp
  convert h using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp [hs.ne']
  ring
/-- `γ_s` has mean zero. -/
theorem solution {s : ℝ} (hs : 0 < s) :
    (∫ y : E, y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = 0 := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hi : Integrable id (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).integrable one_le_two
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
    simpa only [one_mul] using FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable (E := E) hs
  have hfun : (fun z : E => ∫ y, Real.exp ⟪z, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) =
      fun z => Real.exp (‖z‖ ^ 2 / (4 * s)) := funext fun z => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace_readable hs z
  apply ext_inner_left ℝ
  intro v
  rw [inner_zero_right]
  change (innerSL ℝ v) (∫ y, id y ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = 0
  rw [← (innerSL ℝ v).integral_comp_comm hi]
  change (∫ y : E, ⟪v, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = 0
  have hm := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s)
    (by norm_num : (0 : ℝ) < 1) he 1 (fun _ => v)
  rw [hfun] at hm
  have hzero : fderiv ℝ (fun z : E => Real.exp (‖z‖ ^ 2 / (4 * s))) 0 = 0 := by
    rw [(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.hasFDerivAt_exp_norm_sq_div hs (0 : E)).fderiv]
    simp
  simp only [iteratedFDeriv_one_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, pow_one, hzero, zero_apply] at hm
  calc (∫ y : E, ⟪v, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = ∫ y : E, ⟪y, v⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => (real_inner_comm v y).symm
    _ = 0 := hm.symm
