-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.form_signature_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:41.880968+00:00
-- url     : https://prove2.me/submissions/7e3363d4-b005-41dc-a48b-1fab9d6cda9a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_unit_level_volume_pos
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos_MM
import Theorems.Thm_Formalism_FourierDecayAlt_P_jacobian_natural_measure_constant

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
theorem _root_.solution : SigBound := by
  intro P _ B hP hF hK hMs hD hA hJ hNu hI
  have hP0 := hP
  have hU := unit_level_volume_pos hP
  have hμK := pos_μK hP
  have hMM := pos_MM hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hKV, hKt⟩ := hK
  have hc0 : 0 < B.c0 := by unfold MassData.c0; exact div_pos (mul_pos xvN xvH) xpi
  have hc0' : 0 < B.c0' := by unfold MassData.c0'; exact div_pos (mul_pos xvN' xvH') xpi'
  have he1 : 0 ≤ B.e1 := xsd.trans hD
  have hAA : 0 < B.AA := by
    unfold MassData.AA; exact div_pos (mul_pos (mul_pos xB xC) (div_pos hMM xZZ)) hμK
  have hJc := jacobian_natural_measure_constant P B hP0 hJ hNu
  have hIntN : B.IntN ≤ B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg) := by
    rw [hJc]
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (div_nonneg xZZ.le hU.le) (inv_nonneg.mpr xC.le))
  have hKt2 : B.KtopV ≤ (1 + B.δ) * B.IntN / (B.c0 * B.c0') := by
    rw [le_div_iff₀ (mul_pos hc0 hc0')]
    calc B.KtopV * (B.c0 * B.c0') = B.Smod := by unfold MassData.Smod; ring
      _ ≤ _ := hA
  have hEA : 0 ≤ B.e1 * B.AA := mul_nonneg he1 hAA.le
  calc B.Sig = B.ρ0 * B.KV := hF
    _ ≤ B.ρ0 * (B.e1 * B.n0c * B.KtopV) := by
        apply mul_le_mul_of_nonneg_left _ xr.le
        calc B.KV ≤ B.supdens * B.n0c * B.KtopV := hKV
          _ ≤ B.e1 * B.n0c * B.KtopV :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD xn0.le) hKt
    _ = B.e1 * B.AA * B.KtopV := by rw [← hMs]; ring
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * B.IntN / (B.c0 * B.c0')) :=
        mul_le_mul_of_nonneg_left hKt2 hEA
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg)) /
          (B.c0 * B.c0')) := by
        apply mul_le_mul_of_nonneg_left _ hEA
        apply div_le_div_of_nonneg_right _ (mul_pos hc0 hc0').le
        exact mul_le_mul_of_nonneg_left hIntN (by linarith)
    _ = _ := by
        unfold MassData.AA
        have := hc0.ne'; have := hc0'.ne'
        field_simp
end Formalism.FourierDecayAlt.P
