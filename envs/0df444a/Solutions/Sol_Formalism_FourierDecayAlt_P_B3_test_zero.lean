-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.test_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:18.018051+00:00
-- url     : https://prove2.me/submissions/d887be2f-d9da-4b86-bc9b-b0ab21f78c64

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
theorem _root_.solution {w : ℝ → ℝ} (hw : IsTest w) {x : ℝ} (hx : x ≤ 0) : w x = 0 := by
  have hx' : x ∉ tsupport w := fun h => (not_lt.2 hx) (hw.2.2 h)
  by_contra h
  exact hx' (subset_tsupport _ h)
end Formalism.FourierDecayAlt.P.B3
