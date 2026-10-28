-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:08.814851+00:00
-- url     : https://prove2.me/submissions/287e5aac-7a7d-4181-b6d6-37cf35323f85

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_directional_identity_of_bounded_lipschitz_test_readable

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
theorem solution {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {Lh : NNReal}
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (a v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    Integrable (fun z => ⟪z,v⟫ * h (a+z)) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) ∧
    Integrable (fun z => fderiv ℝ h (a+z) v) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) ∧
    (∫ z, ⟪z,v⟫ * h (a+z) ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) =
      (2*s)⁻¹ * ∫ z, fderiv ℝ h (a+z) v ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hf : ContDiff ℝ 1 (fun z : E => h (a+z)) := hh.comp (contDiff_const.add contDiff_id)
  have hp := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test_readable hs hf
    (hhLip.comp ((LipschitzWith.const a).add LipschitzWith.id)) C (fun z => hbound (a+z)) v
  have hd (z : E) : fderiv ℝ (fun w => h (a+w)) z v = fderiv ℝ h (a+z) v := by
    have ha : HasFDerivAt (fun w : E => a+w) (ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).const_add a
    exact congrArg (fun T : E →L[ℝ] ℝ => T v)
      ((hh.differentiable one_ne_zero (a+z)).hasFDerivAt.comp z ha).fderiv
  refine ⟨hp.1,hp.2.1.congr (ae_of_all _ hd),hp.2.2.trans ?_⟩
  congr 1
  exact integral_congr_ae (ae_of_all _ hd)
