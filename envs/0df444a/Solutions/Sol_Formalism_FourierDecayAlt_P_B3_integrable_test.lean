-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.integrable_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:54.112432+00:00
-- url     : https://prove2.me/submissions/c66b56e5-7a28-4a3e-a279-63526bcc0c38

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) {h : ℝ × ℝ → E} (hh : ContinuousOn h Quad) :
    Integrable (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) (volume.restrict Quad) := by
  have hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂) := h₁.2.1.isCompact.prod h₂.2.1.isCompact
  have hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad := prod_mono h₁.2.2 h₂.2.2
  have hc : ContinuousOn (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) (tsupport w₁ ×ˢ tsupport w₂) :=
    (((h₁.1.continuous.comp continuous_fst).mul (h₂.1.continuous.comp continuous_snd)).continuousOn).smul
      (hh.mono hKQ)
  have hs : Function.support (fun τ : ℝ × ℝ => (w₁ τ.1 * w₂ τ.2) • h τ) ⊆ tsupport w₁ ×ˢ tsupport w₂ := by
    intro τ hτ
    refine ⟨subset_tsupport _ fun h0 => hτ ?_, subset_tsupport _ fun h0 => hτ ?_⟩
    · simp [h0]
    · simp [h0]
  exact ((integrableOn_iff_integrable_of_support_subset hs).mp (hc.integrableOn_compact hK)).restrict
end Formalism.FourierDecayAlt.P.B3
