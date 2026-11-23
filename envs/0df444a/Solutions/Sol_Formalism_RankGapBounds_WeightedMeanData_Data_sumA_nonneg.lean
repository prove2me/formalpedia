-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.Data.sumA_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:28.259329+00:00
-- url     : https://prove2.me/submissions/9d73834d-3078-4466-bc22-341fe0069989

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
theorem _root_.solution (hS : D.HidaSetting C) : 0 ≤ D.sumA := by
  obtain ⟨-, -, -, -, -, -, -, haT, -⟩ := hS
  exact Finset.sum_nonneg fun t _ => haT t
end Formalism.RankGapBounds.WeightedMeanData.Data
