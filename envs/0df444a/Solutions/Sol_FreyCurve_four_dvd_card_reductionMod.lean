-- Prove2me | solution 1 for FreyCurve.four_dvd_card_reductionMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4111e444-33a4-591b-8fc2-c5ab08dbae07

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.Algebra.Module.Torsion.Basic
import Theorems.Thm_FreyCurve_card_two_torsion_reductionMod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyCurve_four_dvd_card_reductionMod

open WeierstrassCurve FreyPackage

theorem solution (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    4 ∣ ((FreyPackage.freyCurveInt P).reductionMod q).card := by
  rw [← FreyCurve.card_two_torsion_reductionMod P hq2 hgood]
  exact AddSubgroup.card_dvd_of_injective
    (Submodule.torsionBy ℤ ((freyCurveInt P).reductionMod q).toAffine.Point 2).subtype.toAddMonoidHom
    (fun a b hab => Subtype.ext hab)

end S_FreyCurve_four_dvd_card_reductionMod
end P2MW
export P2MW.S_FreyCurve_four_dvd_card_reductionMod (solution)
