-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_Mreal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:14:51.752622+00:00
-- url     : https://prove2.me/submissions/3594985c-8744-48a8-ae89-bba91db4a9a0

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_Mframe

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}
namespace FriedCrossing.ClusterFrame
theorem _root_.solution (D : FrameData S k) (hdet : ∀ p, (Amat F Jc D p).det ≠ 0) (i j : Fin k) :
    ContDiff ℝ 3 fun q : ℝ × ℝ => Mreal F Jc D q.1 q.2 i j := by
  have : (fun q : ℝ × ℝ => Mreal F Jc D q.1 q.2 i j) =
      fun q : ℝ × ℝ => Complex.reCLM (Mframe F Jc D q i j) := by
    funext q; simp [Mreal, Matrix.map_apply]
  rw [this]
  exact Complex.reCLM.contDiff.comp (contDiff_Mframe F Jc D hdet i j)
end FriedCrossing.ClusterFrame
