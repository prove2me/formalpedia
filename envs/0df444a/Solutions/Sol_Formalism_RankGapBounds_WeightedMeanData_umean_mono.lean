-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.umean_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:26.289021+00:00
-- url     : https://prove2.me/submissions/cb3ae47a-eb87-4588-b305-405659733b31

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {ι : Type} [Fintype ι]
namespace Formalism.RankGapBounds.WeightedMeanData
theorem _root_.solution {X Y : ι → ℝ} (h : ∀ i, X i ≤ Y i) : umean X ≤ umean Y := by
  unfold umean
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ => h i)
    (inv_nonneg.mpr (Nat.cast_nonneg _))
end Formalism.RankGapBounds.WeightedMeanData
