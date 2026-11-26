-- Prove2me | solution 1 for BKAR.Forest.interpolationLevel_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:49.376712+00:00
-- url     : https://prove2.me/submissions/3b956c15-5d9a-45e2-9cab-a1e6f1109380

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevels_min_eq_zero

set_option autoImplicit false
open BKAR
open scoped BigOperators
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    F.interpolationLevel u
        ⟨0, F.interpolationLevels_card_pos u⟩ = 0 := by
  rw [interpolationLevel]
  rw [Finset.orderEmbOfFin_zero rfl (F.interpolationLevels_card_pos u)]
  exact F.interpolationLevels_min_eq_zero u hu
end BKAR.Forest
