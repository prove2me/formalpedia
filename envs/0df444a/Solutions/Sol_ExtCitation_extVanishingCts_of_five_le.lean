-- Prove2me | solution 1 for ExtCitation.extVanishingCts_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f3f6996d-0b34-5ef9-bb33-b9fcc71bc3db

import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_ExtCitation_CyclotomicUnits
import Theorems.Thm_ExtCitation_extVanishingCts_of_e2ClassGroup_and_e2Units
import Theorems.Thm_ExtCitation_Cyclotomic_clGalAction_omegaEigenspace_two_eq_bot
import Theorems.Thm_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_extVanishingCts_of_five_le

set_option autoImplicit false

open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger
open ExtCitation ExtCitation.Cyclotomic

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ExtCitation.ExtVanishingCts p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact extVanishingCts_of_e2ClassGroup_and_e2Units p hp5
    (unitsGalAction p)
    (fun d u => unitsEnd_proj p (clRingAction p (CyclotomicField p ℚ) d) u)
    (clGalAction_omegaEigenspace_two_eq_bot p hp5)
    (fun u heig hloc =>
      unitsOmegaEigenvector_two_eq_zero_of_local_pow p hp5 u heig hloc)

end S_ExtCitation_extVanishingCts_of_five_le
end P2MW
export P2MW.S_ExtCitation_extVanishingCts_of_five_le (solution)
