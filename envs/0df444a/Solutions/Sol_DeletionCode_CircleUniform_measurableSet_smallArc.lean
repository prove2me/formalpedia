-- Prove2me | solution 1 for DeletionCode.CircleUniform.measurableSet_smallArc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:43:30.175204+00:00
-- url     : https://prove2.me/submissions/85c9c733-d5a7-444f-9c62-530ddfb981c3

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
import Theorems.Thm_DeletionCode_CircleUniform_smallArc_eq_ball

set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
namespace DeletionCode.CircleUniform
theorem _root_.solution (Q : ℕ) : MeasurableSet (smallArc Q) := by
  rw [smallArc_eq_ball]
  exact measurableSet_ball
end DeletionCode.CircleUniform
