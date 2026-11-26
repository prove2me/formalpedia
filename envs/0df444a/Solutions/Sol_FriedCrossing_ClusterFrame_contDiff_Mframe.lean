-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_Mframe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:13:26.334264+00:00
-- url     : https://prove2.me/submissions/c16db3a5-f8a3-4c04-96c0-ecf4bf88c06a

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Amat
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Bmat
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_inv_complex
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_mul_complex

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}
namespace FriedCrossing.ClusterFrame
theorem _root_.solution (D : FrameData S k) (hdet : ∀ p, (Amat F Jc D p).det ≠ 0) (l j : Fin k) :
    ContDiff ℝ 3 fun p => Mframe F Jc D p l j := by
  unfold Mframe
  exact contDiff_mul_complex (fun i j => contDiff_inv_complex (contDiff_Amat F Jc D) hdet i j)
    (contDiff_Bmat F Jc D) l j
end FriedCrossing.ClusterFrame
