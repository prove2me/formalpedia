-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_Bmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:11:43.300989+00:00
-- url     : https://prove2.me/submissions/081c08dd-8c7b-4a6c-b67a-38b317c8f374

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
    ContDiff ℝ 3 fun p => Bmat F Jc D p l j := by
  simp only [Bmat, Matrix.of_apply]
  refine contDiff_riesz _ _ _ ?_
  exact (contDiff_snd).mul (contDiff_melem F Jc D.a D.b D.hab (D.φ j) (D.ℓ l))
end FriedCrossing.ClusterFrame
