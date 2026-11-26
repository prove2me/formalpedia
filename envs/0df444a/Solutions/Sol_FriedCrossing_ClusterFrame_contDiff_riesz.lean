-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_riesz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:55.204656+00:00
-- url     : https://prove2.me/submissions/e299af4c-c3c4-4a05-8abb-85f237a6aad1

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ParamInt_contDiff_parametric_intervalIntegral
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_contour

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
namespace FriedCrossing.ClusterFrame
theorem _root_.solution (c : ℂ) (r : ℝ) (g : Param → ℂ) (hg : ContDiff ℝ 3 g) :
    ContDiff ℝ 3 (riesz c r g) := by
  have hint : ContDiff ℝ 3 (Function.uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
      g (p, contour c r t) * Complex.exp (Complex.I * t)) := by
    have hγ : ContDiff ℝ 3 fun q : (ℝ × ℝ) × ℝ => ((q.1, contour c r q.2) : Param) :=
      contDiff_fst.prodMk ((contDiff_contour c r).of_le le_top |>.comp contDiff_snd)
    have he : ContDiff ℝ 3 fun q : (ℝ × ℝ) × ℝ => Complex.exp (Complex.I * (q.2 : ℂ)) :=
      Complex.contDiff_exp.of_le le_top |>.comp
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))
    exact (hg.comp hγ).mul he
  unfold riesz
  exact contDiff_const.mul
    (contDiff_parametric_intervalIntegral (0 : ℝ) (2 * Real.pi) 3 ℂ _ hint)
end FriedCrossing.ClusterFrame
