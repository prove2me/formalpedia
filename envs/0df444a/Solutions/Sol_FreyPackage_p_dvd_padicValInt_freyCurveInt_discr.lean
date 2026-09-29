-- Prove2me | solution 1 for FreyPackage.p_dvd_padicValInt_freyCurveInt_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a586bab4-4169-59f2-9df3-b4bb23cdb080

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_padicValInt_freyCurveInt_discr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr

theorem solution (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : P.p ∣ padicValInt ℓ P.freyCurveInt.Δ :=
  ⟨2 * padicValInt ℓ (P.a * P.b * P.c), by rw [P.padicValInt_freyCurveInt_discr hℓ hℓ2]; ring⟩

end S_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr
end P2MW
export P2MW.S_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr (solution)
