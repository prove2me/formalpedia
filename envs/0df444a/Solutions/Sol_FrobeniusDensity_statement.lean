-- Prove2me | solution 1 for FrobeniusDensity.statement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/737beff3-c5b0-51da-af86-cdd8bbf6e7c2

import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Theorems.Thm_FrobeniusDensity_degOneAsymptotic
import Theorems.Thm_FrobeniusDensity_statement_of_degOneAsymptotic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_statement
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow"

open NumberField

theorem solution (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L :=
  FrobeniusDensity.statement_of_degOneAsymptotic L (FrobeniusDensity.degOneAsymptotic L)

end S_FrobeniusDensity_statement
end P2MW
export P2MW.S_FrobeniusDensity_statement (solution)
