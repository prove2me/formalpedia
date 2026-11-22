-- Prove2me | solution 1 for Csg.attackAction_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:48.444587+00:00
-- url     : https://prove2.me/submissions/943fb51a-4e3f-49e4-805b-67707e1f66c9

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : AttackAction → β) :
    ∑ a : AttackAction, f a = f .attack1 + f .attack2 := by
  have huniv : (Finset.univ : Finset AttackAction) = {AttackAction.attack1, .attack2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
end Csg
