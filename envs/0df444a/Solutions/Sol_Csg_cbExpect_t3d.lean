-- Prove2me | solution 1 for Csg.cbExpect_t3d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:01:04.122061+00:00
-- url     : https://prove2.me/submissions/6c15c0ff-7f4d-4273-a2c0-ecc58bb200e6

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
theorem _root_.solution (a1 : RowMove) (v : CBState → ℝ) :
    cbCSG.expect .t3 a1 .d v = (v .t2 + v .t4) / 2 := by
  change ∑ s', (cbCSG.K .t3 a1 .d s').toReal * v s' = (v .t2 + v .t4) / 2
  rw [show cbCSG.K = cbK from rfl, show cbK .t3 a1 .d = cbCoin .t2 .t4 (by decide) from rfl,
    cbState_sum]
  rw [cbCoin_apply_other .t2 .t4 .t1 (by decide) (by decide) (by decide),
    cbCoin_apply_left .t2 .t4 (by decide),
    cbCoin_apply_other .t2 .t4 .t3 (by decide) (by decide) (by decide),
    cbCoin_apply_right .t2 .t4 (by decide),
    cbCoin_apply_other .t2 .t4 .t5 (by decide) (by decide) (by decide)]
  simp [ENNReal.toReal_inv]
  ring
end Csg
