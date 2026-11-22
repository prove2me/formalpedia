-- Prove2me | solution 1 for Csg.throwerAction_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:24:00.740167+00:00
-- url     : https://prove2.me/submissions/4dafae85-ba72-4f51-ae4f-f18fe40c525d

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : ThrowerAction → β) :
    ∑ a : ThrowerAction, f a = f .wait + f .throw + f .feint := by
  have huniv : (Finset.univ : Finset ThrowerAction) = {ThrowerAction.wait, .throw, .feint} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel
end Csg
