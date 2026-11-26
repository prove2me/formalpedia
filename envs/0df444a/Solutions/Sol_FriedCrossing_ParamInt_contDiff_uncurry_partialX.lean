-- Prove2me | solution 1 for FriedCrossing.ParamInt.contDiff_uncurry_partialX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:42.523385+00:00
-- url     : https://prove2.me/submissions/5dd88056-5776-4a8a-9da6-3f50e1d61a43

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ParamInt
namespace FriedCrossing.ParamInt
theorem _root_.solution {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (n : ℕ)
    (hF : ContDiff ℝ (n + 1) (Function.uncurry F)) :
    ContDiff ℝ n (Function.uncurry (partialX F)) := by
  have : Function.uncurry (partialX F) = fun q : E × ℝ =>
      (fderiv ℝ (Function.uncurry F) q).comp (inl ℝ E ℝ) := by
    funext q; rfl
  rw [this]
  exact (hF.fderiv_right le_rfl).clm_comp contDiff_const
end FriedCrossing.ParamInt
