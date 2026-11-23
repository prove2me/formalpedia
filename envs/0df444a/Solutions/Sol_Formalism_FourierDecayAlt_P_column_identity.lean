-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.column_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:24.683448+00:00
-- url     : https://prove2.me/submissions/b6a2528c-9414-487f-8735-c33d958793e7

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity

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
theorem _root_.solution : Columns := by
  intro P _ B hP hV hL hM hC
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨_, hNa1, hNa1'⟩ := hV
  obtain ⟨hLS, hLSpp, hLS', hLSpp'⟩ := hL
  obtain ⟨hρ, hNaN, hρ', hNaN'⟩ := hM
  obtain ⟨hdd, hG1, hdd', hG1'⟩ := hC
  have eN : B.volN = 1 / B.μN := by rw [eq_div_iff xN.ne', ← hNaN, hNa1]
  have eN' : B.volN' = 1 / B.μN' := by rw [eq_div_iff xN'.ne', ← hNaN', hNa1']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ, eN, hLS]; field_simp
  · rw [hdd, ← hG1, hρ]; field_simp
  · unfold MassData.c0; rw [hdd, hLSpp, eN]; field_simp
  · rw [hρ', eN', hLS']; field_simp
  · rw [hdd', ← hG1', hρ']; field_simp
  · unfold MassData.c0'; rw [hdd', hLSpp', eN']; field_simp
end Formalism.FourierDecayAlt.P
