-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmR_dot_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:34.089494+00:00
-- url     : https://prove2.me/submissions/9e245aa1-866b-4839-b3ab-209ae3e253ec

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
theorem _root_.solution {ι : Type v} (n : ι →₀ ℕ) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ dot n r := by
  unfold dot Finsupp.sum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hr i)
end Formalism.DworkPowerSeriesWeights
