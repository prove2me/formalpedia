-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_inv_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:34.537872+00:00
-- url     : https://prove2.me/submissions/74775347-0a12-4f4e-bd63-3754629f9f4e

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_det_complex
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_adjugate_complex

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
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) (hdet : ∀ x, (A x).det ≠ 0) (i j : n) :
    ContDiff ℝ m fun x => (A x)⁻¹ i j := by
  have : (fun x => (A x)⁻¹ i j) = fun x => ((A x).det)⁻¹ * (A x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  exact ((contDiff_det_complex h).inv hdet).mul (contDiff_adjugate_complex h i j)
end FriedCrossing.ClusterFrame
