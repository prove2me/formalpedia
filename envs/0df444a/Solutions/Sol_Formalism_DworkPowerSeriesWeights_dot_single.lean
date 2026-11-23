-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dot_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:57.742006+00:00
-- url     : https://prove2.me/submissions/2c3657e7-45a0-4a49-b8fd-33d953f95439

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (i : ι) (k : ℕ) (r : ι → ℝ) : dot (Finsupp.single i k) r = k * r i := by
  unfold dot
  rw [Finsupp.sum_single_index (by simp)]
end Formalism.DworkPowerSeriesWeights
