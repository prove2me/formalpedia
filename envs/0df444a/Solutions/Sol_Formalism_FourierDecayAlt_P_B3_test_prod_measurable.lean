-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.test_prod_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:16.92282+00:00
-- url     : https://prove2.me/submissions/c6241ea9-ef99-48ab-9e5f-9a6b110616a8

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
theorem _root_.solution {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Measurable fun τ : ℝ × ℝ => ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) := by
  exact ENNReal.measurable_ofReal.comp ((h₁.1.continuous.measurable.comp measurable_fst).mul
    (h₂.1.continuous.measurable.comp measurable_snd))
end Formalism.FourierDecayAlt.P.B3
