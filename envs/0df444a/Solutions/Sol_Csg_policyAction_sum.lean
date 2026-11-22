-- Prove2me | solution 1 for Csg.policyAction_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:43.544185+00:00
-- url     : https://prove2.me/submissions/940a1853-075c-46b2-9b58-511a65896c51

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : PolicyAction → β) :
    ∑ a : PolicyAction, f a = f .defend1 + f .defend2 := by
  have huniv : (Finset.univ : Finset PolicyAction) = {PolicyAction.defend1, .defend2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
end Csg
