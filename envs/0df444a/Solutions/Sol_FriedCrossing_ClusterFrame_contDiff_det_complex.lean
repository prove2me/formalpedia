-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_det_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:52:50.201823+00:00
-- url     : https://prove2.me/submissions/45574f1b-1dec-41f7-a8dd-7753116b3572

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}
namespace FriedCrossing.ClusterFrame
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : Type*} [Fintype n] [DecidableEq n] {m : WithTop ℕ∞} {A : E → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) : ContDiff ℝ m fun x => (A x).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)
end FriedCrossing.ClusterFrame
