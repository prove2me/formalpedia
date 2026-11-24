-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.lintegral_test_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:04.391555+00:00
-- url     : https://prove2.me/submissions/3261bca4-29bb-4485-a26c-ffc9f8ec7add

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_integrable_test

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p₁ : ∀ x, 0 ≤ w₁ x) (p₂ : ∀ x, 0 ≤ w₂ x)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) (h0 : ∀ τ, 0 ≤ h τ) :
    (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * ENNReal.ofReal (h τ) ∂(volume.restrict Quad)) =
      ENNReal.ofReal (∫ τ, w₁ τ.1 * w₂ τ.2 * h τ ∂(volume.restrict Quad)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (by simpa using integrable_test h₁ h₂ hh)
    (Eventually.of_forall fun τ => mul_nonneg (mul_nonneg (p₁ _) (p₂ _)) (h0 τ))]
  refine lintegral_congr fun τ => ?_
  rw [ENNReal.ofReal_mul (mul_nonneg (p₁ _) (p₂ _))]
end Formalism.FourierDecayAlt.P.B3
