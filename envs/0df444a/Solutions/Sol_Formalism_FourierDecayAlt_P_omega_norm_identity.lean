-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.omega_norm_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:43:59.438627+00:00
-- url     : https://prove2.me/submissions/66bd514b-ab64-4ee3-8d40-4360e96b3585

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.OmNorm := by
  intro V _ _ B x ω z T T' D Dr hH hT hxx hxω hxz hωz hzz hv
  have hωx : B ω x = 0 := by rw [hH x ω, hxω, map_zero]
  have hzx : B z x = 0 := by rw [hH x z, hxz, map_zero]
  have hzω : B z ω = 0 := by rw [hH ω z, hωz, map_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
    hxx, hxω, hxz, hωx, hωz, hzx, hzω, hzz] at hv
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hc : (-D / T) * (starRingEnd ℂ) (-D / T) = (Complex.normSq D : ℂ) / T ^ 2 := by
    rw [map_div₀, map_neg, Complex.conj_ofReal, ← Complex.mul_conj]; field_simp
  have e : B ω ω = -(T' : ℂ) * Complex.normSq Dr + (Complex.normSq D : ℂ) / T ^ 2 * T := by
    rw [← hc]; linear_combination hv
  rw [e]; field_simp; ring
end Formalism.FourierDecayAlt.P
