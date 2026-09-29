-- Prove2me | solution 1 for CuspForm.qCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/573314e4-8e8a-553c-a157-200d4dfffdce

import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_zero

set_option autoImplicit false

theorem solution {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ModularFormClass.qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)

end S_CuspForm_qCoeff_zero
end P2MW
export P2MW.S_CuspForm_qCoeff_zero (solution)
