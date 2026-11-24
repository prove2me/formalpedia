-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.test_prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:57.786772+00:00
-- url     : https://prove2.me/submissions/34a22432-8770-409a-a6a0-bde05c2217dd

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_test_zero

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
theorem _root_.solution {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {τ : ℝ × ℝ} (hτ : τ ∉ Quad) :
    w₁ τ.1 * w₂ τ.2 = 0 := by
  simp only [Quad, Set.mem_prod, Set.mem_Ioi, not_and_or, not_lt] at hτ
  rcases hτ with h | h
  · rw [test_zero h₁ h, zero_mul]
  · rw [test_zero h₂ h, mul_zero]
end Formalism.FourierDecayAlt.P.B3
