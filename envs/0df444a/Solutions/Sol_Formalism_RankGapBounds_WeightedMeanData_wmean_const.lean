-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.wmean_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:00.739915+00:00
-- url     : https://prove2.me/submissions/c815a957-7375-4884-b64e-d5a9b6da01ca

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_sum_pos_of_pos

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
theorem _root_.solution [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ) :
    wmean d (fun _ => c) = c := by
  have hS : ∑ i, d i ≠ 0 := (sum_pos_of_pos hd).ne'
  simp only [wmean]
  rw [div_eq_iff hS, ← Finset.sum_mul]
  ring
end Formalism.RankGapBounds.WeightedMeanData
