-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.umean_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:26.120511+00:00
-- url     : https://prove2.me/submissions/32ad52b1-b918-4bb4-95f0-69a757d2742d

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
theorem _root_.solution [Nonempty ι] (c : ℝ) : umean (fun _ : ι => c) = c := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [umean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [div_eq_iff hc]
  ring
end Formalism.RankGapBounds.WeightedMeanData
