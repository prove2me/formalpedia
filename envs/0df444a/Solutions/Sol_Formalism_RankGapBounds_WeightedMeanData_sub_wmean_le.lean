-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.sub_wmean_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:36.79497+00:00
-- url     : https://prove2.me/submissions/61254fa7-b9c3-4506-bafc-a8f093e94694

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_mono
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_add
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_const

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
theorem _root_.solution [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, c - Y i ≤ X i) : c - wmean d Y ≤ wmean d X := by
  have h1 := wmean_mono (X := fun _ => c) (Y := fun i => X i + Y i) hd
    (fun i => by show c ≤ X i + Y i; linarith [h i])
  have h2 := wmean_add d X Y
  have h3 := wmean_const hd c
  linarith
end Formalism.RankGapBounds.WeightedMeanData
