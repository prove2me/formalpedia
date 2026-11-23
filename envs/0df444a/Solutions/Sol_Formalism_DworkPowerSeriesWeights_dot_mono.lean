-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dot_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:32.709447+00:00
-- url     : https://prove2.me/submissions/16fd11ab-f52f-43ac-b72e-8c4373fe105c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound

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
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (n : ι →₀ ℕ) {r r' : ι → ℝ} (h : ∀ i, r i ≤ r' i) : dot n r ≤ dot n r' := by
  unfold dot Finsupp.sum
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _)
end Formalism.DworkPowerSeriesWeights
