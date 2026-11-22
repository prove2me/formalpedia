-- Prove2me | solution 1 for Csg.cbState_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:01:48.637778+00:00
-- url     : https://prove2.me/submissions/d8533858-78da-4542-8685-aa29a7bf6108

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : CBState → β) :
    ∑ s : CBState, f s = f .t1 + f .t2 + f .t3 + f .t4 + f .t5 := by
  have huniv : (Finset.univ : Finset CBState) = {CBState.t1, .t2, .t3, .t4, .t5} := by decide
  rw [huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel
end Csg
