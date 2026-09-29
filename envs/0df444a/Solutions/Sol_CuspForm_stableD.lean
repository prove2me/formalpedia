-- Prove2me | solution 1 for CuspForm.stableD
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f67dc731-43a3-559a-832c-54bf48b2b6be

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspFormClass_isZeroAt_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_stableD

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    CuspForm.StableD M H k := by
  intro σ f c hc
  exact CuspFormClass.isZeroAt_slash_of_mem_Gamma0 M H k σ f hc

end S_CuspForm_stableD
end P2MW
export P2MW.S_CuspForm_stableD (solution)
