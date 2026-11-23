-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.Data.sum_aT_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:25.698401+00:00
-- url     : https://prove2.me/submissions/58959ceb-8bd6-4c2a-b1ab-ba221303f39c

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
open Formalism.RankGapBounds.WeightedMeanData.Data
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
namespace Formalism.RankGapBounds.WeightedMeanData.Data
theorem _root_.solution (g : ℝ) : ∑ t, D.aT t * g = D.sumA * g := by
  simp only [Data.sumA, Finset.sum_mul]
end Formalism.RankGapBounds.WeightedMeanData.Data
