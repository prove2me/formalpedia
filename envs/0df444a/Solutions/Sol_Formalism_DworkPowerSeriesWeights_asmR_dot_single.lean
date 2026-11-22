-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmR_dot_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:34.086716+00:00
-- url     : https://prove2.me/submissions/2e90cb1f-5909-4c40-84b6-7be8a0907cb0

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {ι : Type v} (i : ι) (k : ℕ) (r : ι → ℝ) :
    dot (Finsupp.single i k) r = (k : ℝ) * r i := by
  unfold dot
  rw [Finsupp.sum_single_index (by simp)]
end Formalism.DworkPowerSeriesWeights
