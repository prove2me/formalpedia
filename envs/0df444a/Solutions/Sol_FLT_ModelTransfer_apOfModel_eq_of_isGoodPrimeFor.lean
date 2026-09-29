-- Prove2me | solution 1 for FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/055c4827-81de-5e39-83ff-3b6d0242d0ee

import Definitions.Def_ModelTransfer_ClearedData
import Theorems.Thm_FLT_ModelTransfer_exists_clearedData_not_dvd
import Theorems.Thm_FLT_ModelTransfer_reducedChange_smul_reductionMod
import Theorems.Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

open WeierstrassCurve FLT.ModelTransfer

theorem solution {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by
  classical
  obtain ⟨D, hD⟩ := exists_clearedData_not_dvd hq hq2 hq3 hC hV hW
  haveI : Fact q.Prime := ⟨hq⟩
  have hred := reducedChange_smul_reductionMod hC D hD
  have hcard : (W.reductionMod q).card = (V.reductionMod q).card :=
    card_eq_of_variableChange_smul_eq hred
  simp only [WeierstrassCurve.apOfModel, WeierstrassCurve.traceOfFrobenius, hcard]

end S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
end P2MW
export P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor (solution)
