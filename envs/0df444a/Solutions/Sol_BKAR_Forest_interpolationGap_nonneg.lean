-- Prove2me | solution 1 for BKAR.Forest.interpolationGap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:38.520458+00:00
-- url     : https://prove2.me/submissions/30b4a54e-da04-44ff-8445-6744db42edcb

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationGap_of_lt

set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    0 ≤ F.interpolationGap u i := by
  rw [F.interpolationGap_of_lt u hi]
  have hle :
      F.interpolationLevel u ⟨i, by omega⟩ ≤
        F.interpolationLevel u ⟨i + 1, by omega⟩ := by
    exact ((F.interpolationLevels u).orderEmbOfFin rfl).monotone (by
      exact Nat.le_succ i)
  exact sub_nonneg.mpr hle
end BKAR.Forest
