-- Prove2me | solution 1 for Csg.cbExpect_pure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:04:03.247405+00:00
-- url     : https://prove2.me/submissions/f57b1e46-7bc7-42d1-bb99-539cff508daa

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbState_sum

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) (s t : CBState) (a1 : RowMove) (a2 : ColMove)
    (h : cbK s a1 a2 = PMF.pure t) : cbCSG.expect s a1 a2 v = v t := by
  change ∑ s', (cbCSG.K s a1 a2 s').toReal * v s' = v t
  rw [show cbCSG.K = cbK from rfl, h, cbState_sum]
  rcases t with _ | _ | _ | _ | _ <;> simp [PMF.pure_apply]
end Csg
