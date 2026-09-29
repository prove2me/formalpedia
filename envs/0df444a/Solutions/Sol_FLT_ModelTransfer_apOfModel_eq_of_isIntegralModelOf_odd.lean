-- Prove2me | solution 1 for FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/86a9b4bb-a9fc-5fc3-966a-0861aca76924

import Definitions.Def_ModelTransfer_ClearedData
import Theorems.Thm_FLT_ModelTransfer_exists_clearedData_not_dvd_odd
import Theorems.Thm_FLT_ModelTransfer_reducedChange_smul_reductionMod
import Theorems.Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf_odd
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

open WeierstrassCurve FLT.ModelTransfer

theorem apOfModel_eq_of_isGoodPrimeFor_odd_local {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by
  classical
  obtain ⟨D, hD⟩ := exists_clearedData_not_dvd_odd hq hq2 hC hV hW
  haveI : Fact q.Prime := ⟨hq⟩
  have hred := reducedChange_smul_reductionMod hC D hD
  have hcard : (W.reductionMod q).card = (V.reductionMod q).card :=
    card_eq_of_variableChange_smul_eq hred
  simp only [WeierstrassCurve.apOfModel, WeierstrassCurve.traceOfFrobenius, hcard]

theorem solution {V W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} {q : ℕ}
    (hVE : V.IsIntegralModelOf E) (hWE : W.IsIntegralModelOf E)
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by
  obtain ⟨C₁, hC₁⟩ := hVE
  obtain ⟨C₂, hC₂⟩ := hWE
  refine apOfModel_eq_of_isGoodPrimeFor_odd_local hq hq2 (C := C₂ * C₁⁻¹) ?_ hV hW
  rw [← hC₁, mul_smul, inv_smul_smul, hC₂]

end S_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf_odd
end P2MW
export P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf_odd (solution)
