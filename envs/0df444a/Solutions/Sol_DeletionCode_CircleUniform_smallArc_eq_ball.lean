-- Prove2me | solution 1 for DeletionCode.CircleUniform.smallArc_eq_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:41.764194+00:00
-- url     : https://prove2.me/submissions/d86d1a57-97a6-48eb-b500-f20f57bc096e

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution (Q : ℕ) :
    smallArc Q = Metric.ball (0 : UnitAddCircle) (1 / (Q : ℝ)) := by
  ext z
  simp only [smallArc, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
end DeletionCode.CircleUniform
