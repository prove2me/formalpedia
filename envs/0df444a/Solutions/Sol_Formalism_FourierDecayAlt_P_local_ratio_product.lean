-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.local_ratio_product
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:35.020806+00:00
-- url     : https://prove2.me/submissions/371ca945-9c33-4f1f-8cdd-99908f03b8cb

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_gamma_product_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_middle_level_volume_index

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
theorem _root_.solution : LocalProduct := by
  intro P _ B hP hO hT hI
  have hP0 := hP
  have hG1 := gamma_product_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hMo : B.Mo = B.μKo ^ 2 / (B.μSo * B.μSo') * B.localVolumeArchimedean := by
    rw [← hO]; field_simp
  have hM : ∏ p, B.Mp p = (∏ p, B.localVolumeAtPlace p) * (∏ p, B.μKp p) * (∏ p, B.μKnatp p) /
      ((∏ p, B.μSp p) * ∏ p, B.μSp' p) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
    refine prod_congr rfl fun p _ => ?_
    obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff qU.ne'] at h
    rw [h]; field_simp
  have hKn : ∏ p, B.μKnatp p = B.Gam1 * ∏ p, B.μKppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => middle_level_volume_index P B hP0 hI p
  have hSp : ∏ p, B.μSp p = B.Gam1 * ∏ p, B.μSppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.1
  have hSp' : ∏ p, B.μSp' p = B.Gam1 * ∏ p, B.μSppp' p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.2
  have a1 : 0 < ∏ p, B.localVolumeAtPlace p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2
  have a2 : 0 < ∏ p, B.μKp p := prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have a3 : 0 < ∏ p, B.μKppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1
  have a4 : 0 < ∏ p, B.μSppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1
  have a5 : 0 < ∏ p, B.μSppp' p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKpp MassData.μSpp MassData.μSpp' MassData.μKnat MassData.μS MassData.μS'
  rw [hM, hMo, hKn, hSp, hSp']
  constructor <;> field_simp <;> ring
end Formalism.FourierDecayAlt.P
