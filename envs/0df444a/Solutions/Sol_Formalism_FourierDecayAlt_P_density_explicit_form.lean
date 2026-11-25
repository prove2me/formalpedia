-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_explicit_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:35:41.466273+00:00
-- url     : https://prove2.me/submissions/6523bbc1-b669-4f4e-a64f-1ad3f140d9ee

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_unit_level_volume_pos
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__K_44911b469fcc
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos_MM
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__S_22dd14f18b19
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__S__1bd351e7cc0b
import Theorems.Thm_Formalism_FourierDecayAlt_P_local_ratio_product

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
theorem _root_.solution : NN0Formula := by
  intro P _ B hP hV hL hM hO hT hI
  obtain ⟨_, hLP⟩ := local_ratio_product P B hP hO hT hI
  have hμK := pos_μK hP
  have hMM := pos_MM hP
  have hU := unit_level_volume_pos hP
  have hS := pos_μS hP
  have hS' := pos_μS' hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hVB, hNa1, hNa1'⟩ := hV
  obtain ⟨hLS, _, hLS', _⟩ := hL
  obtain ⟨hρ, hNaN, hρ', hNaN'⟩ := hM
  have eN : B.volN = 1 / B.μN := by rw [eq_div_iff xN.ne', ← hNaN, hNa1]
  have eN' : B.volN' = 1 / B.μN' := by rw [eq_div_iff xN'.ne', ← hNaN', hNa1']
  have hKn : B.μKnat = B.μK * ∏ p, B.glk p * B.nn p / B.gg p := by
    unfold MassData.μKnat MassData.μK
    have : ∏ p, B.μKnatp p = ∏ p, (B.μKp p * (B.glk p * B.nn p / B.gg p)) :=
      prod_congr rfl fun p _ => by
        obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
        have h := (hI p).2
        rw [div_eq_iff qKp.ne'] at h
        rw [h]; ring
    rw [this, prod_mul_distrib]; ring
  have e1 : B.MM = B.μKnat / (B.μS * B.μS') * B.μK * B.unitLevelVolume := by
    rw [← hLP]; field_simp
  have eB : B.volB = B.volHa * B.volHa' / B.volG := by rw [eq_div_iff xG.ne']; exact hVB
  unfold MassData.nn0 MassData.V0
  rw [e1, hKn, eB, hρ, hρ', eN, eN', hLS, hLS']
  field_simp
end Formalism.FourierDecayAlt.P
