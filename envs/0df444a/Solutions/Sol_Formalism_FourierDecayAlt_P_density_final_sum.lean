-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_final_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:35:44.755789+00:00
-- url     : https://prove2.me/submissions/aa7f6dfd-c3a2-40fe-b5b8-c89f10f94c79

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos__Kpp_87a350d555d2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_gamma_product_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos_idx

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
theorem _root_.solution : VolumeMassSum := by
  intro P _ B hP hV hL hM hC hI
  have hG1p := gamma_product_pos hP
  have hKpp := pos_μKpp hP
  have hidx := pos_idx hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hρ, _, hρ', _⟩ := hM
  obtain ⟨hdd, hG1, hdd', hG1'⟩ := hC
  have hK : B.μK = (∏ p, B.gg p / (B.nn p * B.uk p)) * B.μKpp := by
    unfold MassData.μK MassData.μKpp
    have : ∏ p, B.μKp p = ∏ p, (B.gg p / (B.nn p * B.uk p) * B.μKppp p) :=
      prod_congr rfl fun p _ => (hI p).1
    rw [this, prod_mul_distrib]; ring
  have hprod : (∏ p, B.ga p * (B.glk p * B.nn p) / B.gg p) =
      B.Gam1 * ∏ p, B.glk p * B.nn p / B.gg p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => by ring
  have hI2 : (∏ p, B.glk p * B.nn p / B.gg p) * (∏ p, B.gg p / (B.nn p * B.uk p)) = B.Gam1 := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
    unfold MassData.ga
    field_simp
  have hd2 : B.d = B.Gam1 * B.ρ0 * B.dimπ := by rw [hdd, ← hG1, hρ]; field_simp
  have hd2' : B.d' = B.Gam1 * B.ρ0' * B.dimπ' := by rw [hdd', ← hG1', hρ']; field_simp
  unfold MassData.V0 MassData.Dstar
  rw [hprod, hK, hd2, hd2', ← hI2]
  field_simp
end Formalism.FourierDecayAlt.P
