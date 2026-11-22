-- Prove2me | solution 1 for Csg.skirmishState_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:44:02.109655+00:00
-- url     : https://prove2.me/submissions/f0bde935-95f7-4d61-94fd-fcb18df35f12

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : SkirmishState → β) :
    ∑ s : SkirmishState, f s = f .hide + f .home + f .wet := by
  have huniv : (Finset.univ : Finset SkirmishState) = {SkirmishState.hide, .home, .wet} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel
end Csg
