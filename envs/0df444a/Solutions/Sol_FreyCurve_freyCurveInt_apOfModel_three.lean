-- Prove2me | solution 1 for FreyCurve.freyCurveInt_apOfModel_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3a705ce1-b3f1-544c-b894-2fbdd9270f0c

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyCurve_four_dvd_card_reductionMod
import Theorems.Thm_WeierstrassCurve_card_pos
import Theorems.Thm_WeierstrassCurve_card_le_two_mul_add_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyCurve_freyCurveInt_apOfModel_three

open WeierstrassCurve FreyPackage

theorem solution (P : FreyPackage)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor 3) :
    (FreyPackage.freyCurveInt P).apOfModel 3 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 4 ∣ ((freyCurveInt P).reductionMod 3).card :=
    FreyCurve.four_dvd_card_reductionMod P (by decide) hgood
  have hpos : 0 < ((freyCurveInt P).reductionMod 3).card :=
    ((freyCurveInt P).reductionMod 3).card_pos
  have hle : ((freyCurveInt P).reductionMod 3).card ≤ 2 * Nat.card (ZMod 3) + 1 :=
    ((freyCurveInt P).reductionMod 3).card_le_two_mul_add_one
  rw [Nat.card_zmod] at hle

  have hcase : ((freyCurveInt P).reductionMod 3).card = 4 := by omega

  simp only [apOfModel, traceOfFrobenius, hcase, Nat.card_zmod]
  norm_num

end S_FreyCurve_freyCurveInt_apOfModel_three
end P2MW
export P2MW.S_FreyCurve_freyCurveInt_apOfModel_three (solution)
