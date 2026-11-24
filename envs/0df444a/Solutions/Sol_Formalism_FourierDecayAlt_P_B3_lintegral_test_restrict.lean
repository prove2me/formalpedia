-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.lintegral_test_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:48.309662+00:00
-- url     : https://prove2.me/submissions/7169fba8-5035-4a0f-b194-ff538231c515

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_measurableSet_Quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_test_prod_zero

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
theorem _root_.solution {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ τ : ℝ × ℝ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * F τ) =
      ∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * F τ ∂(volume.restrict Quad) := by
  rw [← lintegral_indicator (hs := measurableSet_Quad)]
  congr 1
  funext τ
  by_cases hτ : τ ∈ Quad
  · rw [Set.indicator_of_mem hτ]
  · rw [test_prod_zero h₁ h₂ hτ, ENNReal.ofReal_zero, zero_mul]
    simp [Set.indicator, hτ]
end Formalism.FourierDecayAlt.P.B3
