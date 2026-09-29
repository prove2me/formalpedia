-- Prove2me | solution 1 for FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9e9c3fa6-ad53-5b6b-bd53-7dc78d73935a

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_FreyPackage_frey_isSemistableModel
import Theorems.Thm_FreyPackage_freyCurveInt_map
import Theorems.Thm_FreyPackage_dvd_freyCurveInt_discr_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_c₄ map variableChange_Δ variableChange_c₄ map_Δ Δ c₄ VariableChange j IsGoodPrimeFor IsSemistableModel IsIntegralModelOf"
p2m_open "WeierstrassCurve"

variable {V W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ}

theorem c₄_pow_three_mul_Δ_eq_of_isIntegralModelOf
    (hV : V.IsIntegralModelOf E) (hW : W.IsIntegralModelOf E) :
    V.c₄ ^ 3 * W.Δ = W.c₄ ^ 3 * V.Δ := by
  obtain ⟨C₁, hC₁⟩ := hV
  obtain ⟨C₂, hC₂⟩ := hW
  have hVc₄ : (V.map (Int.castRingHom ℚ)).c₄ = ((V.c₄ : ℤ) : ℚ) := by
    rw [map_c₄]; simp
  have hWc₄ : (W.map (Int.castRingHom ℚ)).c₄ = ((W.c₄ : ℤ) : ℚ) := by
    rw [map_c₄]; simp
  have hVΔ : (V.map (Int.castRingHom ℚ)).Δ = ((V.Δ : ℤ) : ℚ) := by
    rw [map_Δ]; simp
  have hWΔ : (W.map (Int.castRingHom ℚ)).Δ = ((W.Δ : ℤ) : ℚ) := by
    rw [map_Δ]; simp

  set D : VariableChange ℚ := C₂ * C₁⁻¹ with hD
  have hDV : D • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ) := by
    rw [hD, ← hC₁, mul_smul, inv_smul_smul, hC₂]

  have hc₄ : ((W.c₄ : ℤ) : ℚ) = (↑D.u⁻¹ : ℚ) ^ 4 * ((V.c₄ : ℤ) : ℚ) := by
    rw [← hWc₄, ← hDV, variableChange_c₄, hVc₄]
  have hΔ : ((W.Δ : ℤ) : ℚ) = (↑D.u⁻¹ : ℚ) ^ 12 * ((V.Δ : ℤ) : ℚ) := by
    rw [← hWΔ, ← hDV, variableChange_Δ, hVΔ]

  have key : (((V.c₄ ^ 3 * W.Δ : ℤ)) : ℚ) = (((W.c₄ ^ 3 * V.Δ : ℤ)) : ℚ) := by
    push_cast
    rw [hc₄, hΔ]
    ring
  exact_mod_cast key

theorem dvd_Δ_of_isIntegralModelOf_of_isSemistableModel
    (hV : V.IsIntegralModelOf E) (hW : W.IsIntegralModelOf E)
    (hss : V.IsSemistableModel) {ℓ : ℕ} (hℓ : ℓ.Prime) (hbad : (ℓ : ℤ) ∣ V.Δ) :
    (ℓ : ℤ) ∣ W.Δ := by
  have hcross := c₄_pow_three_mul_Δ_eq_of_isIntegralModelOf hV hW
  have hℓc₄ : ¬ (ℓ : ℤ) ∣ V.c₄ := hss ℓ hℓ hbad
  have hℓc₄3 : ¬ (ℓ : ℤ) ∣ V.c₄ ^ 3 :=
    fun h => hℓc₄ (Int.Prime.dvd_pow' hℓ h)
  have hdvd : (ℓ : ℤ) ∣ V.c₄ ^ 3 * W.Δ := hcross ▸ (hbad.mul_left _)
  exact (Int.Prime.dvd_mul' hℓ hdvd).resolve_left hℓc₄3

end WeierstrassCurve

namespace FreyPackage
p2m_export "FreyPackage" "freyCurveInt freyCurve c a b frey_isSemistableModel freyCurveInt_map dvd_freyCurveInt_discr_iff"
p2m_open "FreyPackage"

p2m_open "WeierstrassCurve P2MW.S_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve.WeierstrassCurve"

private theorem _root_.FreyPackage.freyCurveInt_isIntegralModelOf (P : FreyPackage) :
    P.freyCurveInt.IsIntegralModelOf P.freyCurve :=
  ⟨1, by rw [one_smul, P.freyCurveInt_map]⟩

p2m_export "FreyPackage" "freyCurveInt_isIntegralModelOf"

private theorem _root_.FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve' (P : FreyPackage)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf P.freyCurve)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓabc : (ℓ : ℤ) ∣ P.a * P.b * P.c) :
    ¬ W.IsGoodPrimeFor ℓ :=
  fun hgood => hgood <|
    dvd_Δ_of_isIntegralModelOf_of_isSemistableModel
      P.freyCurveInt_isIntegralModelOf hW P.frey_isSemistableModel hℓ
      ((P.dvd_freyCurveInt_discr_iff hℓ).mpr hℓabc)

p2m_export "FreyPackage" "not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve'"
end FreyPackage

theorem solution (P : FreyPackage) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf P.freyCurve)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓabc : (ℓ : ℤ) ∣ P.a * P.b * P.c) : ¬ W.IsGoodPrimeFor ℓ :=
  P.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve' hW hℓ hℓabc

end S_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve
end P2MW
export P2MW.S_FreyPackage_not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve (solution)
