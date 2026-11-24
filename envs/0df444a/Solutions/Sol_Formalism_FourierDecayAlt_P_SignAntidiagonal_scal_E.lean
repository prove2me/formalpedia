-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.scal_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:06.610062+00:00
-- url     : https://prove2.me/submissions/49233026-50f9-47d5-a544-2d916b38fb51

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (dh t σ ε : ℂ) (s' : ℕ) (hdh : dh ≠ 0) (ht : t ≠ 0) (hσ : σ * σ = 1) (hε : ε * ε = 1) :
    (dh * t ^ (s' + 1) * (ε * σ))⁻¹ * (dh * t ^ s' * σ) = ε * t⁻¹ * (dh⁻¹ * dh) := by
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, zero_mul] at hσ; exact zero_ne_one hσ
  have hε0 : ε ≠ 0 := by intro h0; rw [h0, zero_mul] at hε; exact zero_ne_one hε
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
  rw [mul_inv, mul_inv, mul_inv, hεi, inv_mul_cancel₀ hdh, pow_succ]
  field_simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
