-- Prove2me | solution 1 for FriedCrossing.ParamInt.hasFDerivAt_partialX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:14.262973+00:00
-- url     : https://prove2.me/submissions/b33c2b62-2757-4ad7-b76f-74dd1dc4ba98

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
    (hF : ContDiff ℝ (n + 1) (Function.uncurry F)) (x : E) (t : ℝ) :
    HasFDerivAt (fun x => F x t) (partialX F x t) x := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (x, t)) (x, t) :=
    ((hF.differentiable (by simp)) (x, t)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : E => ((x, t) : E × ℝ)) (inl ℝ E ℝ) x := hasFDerivAt_prodMk_left x t
  exact h1.comp x h2
end FriedCrossing.ParamInt
