-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_adjugate_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:25.088928+00:00
-- url     : https://prove2.me/submissions/009f2371-b633-42ab-9710-f35783e1151f

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ClusterFrame_contDiff_det_complex

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
    (h : ∀ i j, ContDiff ℝ m fun x => A x i j) (i j : n) :
    ContDiff ℝ m fun x => (A x).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det_complex fun i' j' => ?_
  rcases eq_or_ne i' j with rfl | hne
  · simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne hne]; exact h i' j'
end FriedCrossing.ClusterFrame
