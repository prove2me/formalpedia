-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_contour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:14.762798+00:00
-- url     : https://prove2.me/submissions/217ef976-5cae-4177-8f6f-ade82f44d425

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
namespace FriedCrossing.ClusterFrame
theorem _root_.solution (c : ℂ) (r : ℝ) : ContDiff ℝ ⊤ fun t : ℝ => contour c r t := by
  unfold contour
  refine contDiff_const.add (contDiff_const.mul (Complex.contDiff_exp.comp ?_))
  exact contDiff_const.mul Complex.ofRealCLM.contDiff
end FriedCrossing.ClusterFrame
