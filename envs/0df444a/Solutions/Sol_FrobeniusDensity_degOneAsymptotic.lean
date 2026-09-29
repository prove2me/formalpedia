-- Prove2me | solution 1 for FrobeniusDensity.degOneAsymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5dfaa324-12eb-5aa4-98a7-5cf0ddca4398

import Theorems.Thm_FrobeniusDensity_degOneSum_add_log_isBigO
import Theorems.Thm_FrobeniusDensity_summable_degOne_term
import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_degOneAsymptotic

set_option autoImplicit false

open NumberField

theorem solution (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := fun H S₀ =>
  ⟨fun _ hs => FrobeniusDensity.summable_degOne_term
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀ hs,
    FrobeniusDensity.degOneSum_add_log_isBigO
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀⟩

end S_FrobeniusDensity_degOneAsymptotic
end P2MW
export P2MW.S_FrobeniusDensity_degOneAsymptotic (solution)
