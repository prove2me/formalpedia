-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.integral_test_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:53.464716+00:00
-- url     : https://prove2.me/submissions/320aeca3-1999-4633-84b6-343f346a8146

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_integrable_test
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_contOn_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_contOn_neg

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
theorem _root_.solution {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) :
    (∫ τ, w₁ τ.1 * w₂ τ.2 * h τ ∂(volume.restrict Quad)) =
      (∫ τ, w₁ τ.1 * w₂ τ.2 * max (h τ) 0 ∂(volume.restrict Quad)) -
        ∫ τ, w₁ τ.1 * w₂ τ.2 * max (-h τ) 0 ∂(volume.restrict Quad) := by
  rw [← integral_sub (by simpa using integrable_test h₁ h₂ (contOn_pos hh))
    (by simpa using integrable_test h₁ h₂ (contOn_neg hh))]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
end Formalism.FourierDecayAlt.P.B3
