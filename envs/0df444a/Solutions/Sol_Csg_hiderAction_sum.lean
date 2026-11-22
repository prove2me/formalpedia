-- Prove2me | solution 1 for Csg.hiderAction_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:24:00.216872+00:00
-- url     : https://prove2.me/submissions/94586ed7-9ff0-4171-89c5-0aa569102a12

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : HiderAction → β) :
    ∑ a : HiderAction, f a = f .hide + f .run := by
  have huniv : (Finset.univ : Finset HiderAction) = {HiderAction.hide, .run} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
end Csg
