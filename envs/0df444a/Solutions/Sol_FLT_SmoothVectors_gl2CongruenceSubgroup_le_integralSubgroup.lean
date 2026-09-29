-- Prove2me | solution 1 for FLT.SmoothVectors.gl2CongruenceSubgroup_le_integralSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0f853e7c-da8b-52ab-a9b3-3a34e0737b25

import Mathlib
import Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Theorems.Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup

open FLT.SmoothVectors

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
  rw [← gl2CongruenceSubgroup_zero_eq_integralSubgroup p]
  exact gl2CongruenceSubgroup_antitone p (Nat.zero_le n)

end S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup
end P2MW
export P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup (solution)
