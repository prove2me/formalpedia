-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.box_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:25:52.52077+00:00
-- url     : https://prove2.me/submissions/5f667043-e775-4406-a1bb-a61a29dc5652

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_big

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
theorem _root_.solution (f : ℝ × ℝ → ℝ≥0∞) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (τ : ℝ × ℝ) :
    (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂).indicator f τ ≤
      ENNReal.ofReal (pl (a₁ / 2) (b₁ + 1) (2 / a₁ + 1) τ.1 * pl (a₂ / 2) (b₂ + 1) (2 / a₂ + 1) τ.2) * f τ := by
  by_cases hτ : τ ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂
  · rw [Set.indicator_of_mem hτ, pl_big h₁ hτ.1, pl_big h₂ hτ.2, mul_one, ENNReal.ofReal_one, one_mul]
  · simp [Set.indicator, hτ]
end Formalism.FourierDecayAlt.P.B3
