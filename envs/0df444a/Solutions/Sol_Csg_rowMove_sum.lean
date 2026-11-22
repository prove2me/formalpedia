-- Prove2me | solution 1 for Csg.rowMove_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:54:38.636405+00:00
-- url     : https://prove2.me/submissions/e82de47f-3eb8-4de1-9d39-347fefce60e4

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : RowMove → β) :
    ∑ a : RowMove, f a = f .b + f .d := by
  have huniv : (Finset.univ : Finset RowMove) = {RowMove.b, .d} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
end Csg
