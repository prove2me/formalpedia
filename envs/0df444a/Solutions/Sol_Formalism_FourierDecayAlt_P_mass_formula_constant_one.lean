-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.mass_formula_constant_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:53.8342+00:00
-- url     : https://prove2.me/submissions/daa2b0dd-1206-404d-bcb1-9b1067323955

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_unit_level_volume_pos
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Spp_e82dfb079d22
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Spp__8d73f9415947
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_gamma_product_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos_tt
import Theorems.Thm_Formalism_FourierDecayAlt_P_column_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_local_ratio_product
import Theorems.Thm_Formalism_FourierDecayAlt_P_form_signature_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
open LocalVolumePositivity
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : MainTheorem := by
  intro P _ B hP h2A hF hK hMs hD hA hJ hNu hI hV hL hM hC hO hT hIx
  have hSB := form_signature_bound P B hP hF hK hMs hD hA hJ hNu hI
  obtain ⟨_, cd, cc, _, cd', cc'⟩ := column_identity P B hP hV hL hM hC
  obtain ⟨hLP, _⟩ := local_ratio_product P B hP hO hT hIx
  have htt := pos_tt hP
  have hG1 := gamma_product_pos hP
  have hμK := pos_μK hP
  have hKpp := pos_μKpp hP
  have hSpp := pos_μSpp hP
  have hSpp' := pos_μSpp' hP
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hGS : B.GS = B.tt * B.Gam1 * B.Sig := by
    unfold MassData.GS; rw [hF, cd]; field_simp
  have key : B.tt * B.Gam1 * ((1 + B.δ) * B.e1 * (B.c0 * B.c0')⁻¹ * B.volB * (B.MM / B.unitLevelVolume) /
      (B.μK * B.deg)) = (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) := by
    have e1 : B.MM / B.unitLevelVolume = B.μKpp / (B.Gam1 * B.μSpp * B.μSpp') * B.μK := by
      rw [← hLP]; field_simp
    have e2 : (B.c0)⁻¹ = B.d * B.μSpp / B.volHa := by rw [← cc, one_div]
    have e3 : (B.c0')⁻¹ = B.d' * B.μSpp' / B.volHa' := by rw [← cc', one_div]
    have e4 : B.volB = B.volHa * B.volHa' / B.volG := by rw [eq_div_iff xG.ne']; exact hV.1
    unfold MassData.Dstar
    rw [mul_inv, e1, e2, e3, e4]
    field_simp
  refine ⟨hGS, ?_, ?_⟩
  · rw [hGS, ← key]
    exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le
  · calc B.Kgs2 ≤ B.tt * B.Gam1 * B.Sig := h2A
      _ ≤ _ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le
end Formalism.FourierDecayAlt.P
