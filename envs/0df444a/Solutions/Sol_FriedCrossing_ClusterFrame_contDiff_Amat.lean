-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_Amat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:11:42.181153+00:00
-- url     : https://prove2.me/submissions/a300fc40-2093-460b-ac5b-36194f9c11c8

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_melem
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_riesz

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}
namespace FriedCrossing.ClusterFrame
theorem _root_.solution (D : FrameData S k) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Amat F Jc D p l j := by
  simp only [Amat, Matrix.of_apply]
  exact contDiff_riesz _ _ _ (contDiff_melem F Jc D.a D.b D.hab (D.φ j) (D.ℓ l))
end FriedCrossing.ClusterFrame
