-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_melem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:58.792529+00:00
-- url     : https://prove2.me/submissions/fa0705f5-c47d-49da-81d7-a9327a17417d

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_Scale_contDiff_loss


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
namespace FriedCrossing.ClusterFrame
theorem _root_.solution (a b : ℕ) (hab : b + 15 ≤ a) (φ : S.H a) (ℓ : S.H b →L[ℝ] ℝ) :
    ContDiff ℝ 3 (melem F Jc a b (by omega) φ ℓ) := by
  have hT : ContDiff ℝ 3 fun x => (S.incl a b (by omega)).comp (F.R a x) :=
    contDiff_loss F 3 a b (by simpa [lossBudget] using hab)
  have h1 : ContDiff ℝ 3 fun x => ℓ (((S.incl a b (by omega)).comp (F.R a x)) φ) :=
    contDiff_const.clm_apply (hT.clm_apply contDiff_const)
  have h2 : ContDiff ℝ 3 fun x => ℓ (Jc.J b (((S.incl a b (by omega)).comp (F.R a x)) φ)) :=
    contDiff_const.clm_apply (contDiff_const.clm_apply (hT.clm_apply contDiff_const))
  unfold melem
  exact (Complex.ofRealCLM.contDiff.comp h1).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h2))
end FriedCrossing.ClusterFrame
