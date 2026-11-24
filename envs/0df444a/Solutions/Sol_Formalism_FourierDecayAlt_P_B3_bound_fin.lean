-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.bound_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:46.937012+00:00
-- url     : https://prove2.me/submissions/14b80433-2867-4176-961b-e54faa5dfade

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_isTest

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
theorem _root_.solution {f : ℝ × ℝ → ℝ≥0∞} (hfin : FinT f) {a₁ a₂ : ℝ} (b₁ b₂ : ℝ) (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    (∫⁻ τ, ENNReal.ofReal (pl (a₁ / 2) (b₁ + 1) (2 / a₁ + 1) τ.1 * pl (a₂ / 2) (b₂ + 1) (2 / a₂ + 1) τ.2) * f τ
      ∂(volume.restrict Quad)) ≠ ∞ := by
  have hk₁ : (0:ℝ) ≤ 2 / a₁ + 1 := by have := div_pos two_pos h₁; linarith
  have hk₂ : (0:ℝ) ≤ 2 / a₂ + 1 := by have := div_pos two_pos h₂; linarith
  exact hfin _ _ (pl_isTest (by linarith) hk₁) (pl_isTest (by linarith) hk₂) (pl_nonneg _ _ _) (pl_nonneg _ _ _)
end Formalism.FourierDecayAlt.P.B3
