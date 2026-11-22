-- Prove2me | solution 1 for Csg.rpsAction_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:37.357572+00:00
-- url     : https://prove2.me/submissions/0dc816f3-a5ce-4d65-99d6-ee47b26ab967

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : RPSAction → β) :
    ∑ a : RPSAction, f a = f .rock + f .paper + f .scissors := by
  have huniv : (Finset.univ : Finset RPSAction) = {RPSAction.rock, RPSAction.paper, .scissors} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]
end Csg
