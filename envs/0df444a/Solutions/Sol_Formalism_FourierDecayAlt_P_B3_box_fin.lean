-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.box_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:44:57.141792+00:00
-- url     : https://prove2.me/submissions/6be9ed1f-d825-4b49-bf17-62c307a03bf2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_bound_fin

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
    ((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) ≠ ∞ := by
  have hS : MeasurableSet (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) := measurableSet_Ioo.prod measurableSet_Ioo
  rw [withDensity_apply _ hS, ← lintegral_indicator (hs := hS)]
  exact ne_top_of_le_ne_top (bound_fin hfin b₁ b₂ h₁ h₂) (lintegral_mono (box_bound f h₁ h₂))
end Formalism.FourierDecayAlt.P.B3
