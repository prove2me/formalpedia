-- Prove2me | solution 1 for FriedCrossing.ClusterFrame.contDiff_mul_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:38.67313+00:00
-- url     : https://prove2.me/submissions/3718b1f9-e140-480b-9397-a414cf61c41e

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
    {n : Type*} [Fintype n] {m : WithTop ℕ∞} {A B : E → Matrix n n ℂ}
    (hA : ∀ i j, ContDiff ℝ m fun x => A x i j) (hB : ∀ i j, ContDiff ℝ m fun x => B x i j)
    (i j : n) : ContDiff ℝ m fun x => (A x * B x) i j := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ => (hA i l).mul (hB l j)
end FriedCrossing.ClusterFrame
