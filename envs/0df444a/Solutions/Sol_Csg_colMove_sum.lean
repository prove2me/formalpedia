-- Prove2me | solution 1 for Csg.colMove_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:55:36.269929+00:00
-- url     : https://prove2.me/submissions/4f0b7145-93c0-4778-aa52-00d82afd8b61

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : ColMove → β) :
    ∑ a : ColMove, f a = f .c + f .d := by
  have huniv : (Finset.univ : Finset ColMove) = {ColMove.c, .d} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
end Csg
