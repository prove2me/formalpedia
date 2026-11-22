-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmR_dot_fintype
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:25.089826+00:00
-- url     : https://prove2.me/submissions/8c9d8317-0ee6-4c00-809c-734809efb868

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
theorem _root_.solution {ι : Type v} [Fintype ι] (n : ι →₀ ℕ) (r : ι → ℝ) :
    dot n r = ∑ i, (n i : ℝ) * r i := by
  unfold dot
  exact Finsupp.sum_fintype _ _ (fun i => by simp)
end Formalism.DworkPowerSeriesWeights
