-- Prove2me | solution 1 for Csg.cbExpect_t2d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:59.932086+00:00
-- url     : https://prove2.me/submissions/7146b256-aeef-46d4-8bc2-2e6ae9371567

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_cbState_sum
import Theorems.Thm_Csg_cbCoin_apply_left
import Theorems.Thm_Csg_cbCoin_apply_right
import Theorems.Thm_Csg_cbCoin_apply_other

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (a2 : ColMove) (v : CBState → ℝ) :
    cbCSG.expect .t2 .d a2 v = (v .t1 + v .t3) / 2 := by
  change ∑ s', (cbCSG.K .t2 .d a2 s').toReal * v s' = (v .t1 + v .t3) / 2
  rw [show cbCSG.K = cbK from rfl, show cbK .t2 .d a2 = cbCoin .t1 .t3 (by decide) from rfl,
    cbState_sum]
  rw [cbCoin_apply_left .t1 .t3 (by decide),
    cbCoin_apply_other .t1 .t3 .t2 (by decide) (by decide) (by decide),
    cbCoin_apply_right .t1 .t3 (by decide),
    cbCoin_apply_other .t1 .t3 .t4 (by decide) (by decide) (by decide),
    cbCoin_apply_other .t1 .t3 .t5 (by decide) (by decide) (by decide)]
  simp [ENNReal.toReal_inv]
  ring
end Csg
