-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.wmean_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:26.721145+00:00
-- url     : https://prove2.me/submissions/b64c140f-2ca3-42dc-9678-ab2ec0fd2a12

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
theorem _root_.solution {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) (h : ∀ i, X i ≤ Y i) :
    wmean d X ≤ wmean d Y := by
  unfold wmean
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hd i).le)
    (inv_nonneg.mpr (Finset.sum_nonneg fun i _ => (hd i).le))
end Formalism.RankGapBounds.WeightedMeanData
