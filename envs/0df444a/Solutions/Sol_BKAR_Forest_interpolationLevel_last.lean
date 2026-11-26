-- Prove2me | solution 1 for BKAR.Forest.interpolationLevel_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:57.530707+00:00
-- url     : https://prove2.me/submissions/1e01c0ed-0d91-40aa-ac8d-494ea479dfb9

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevels_max_eq_one

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
        ⟨(F.interpolationLevels u).card - 1,
          Nat.sub_lt (F.interpolationLevels_card_pos u) Nat.zero_lt_one⟩ = 1 := by
  rw [interpolationLevel]
  rw [Finset.orderEmbOfFin_last rfl (F.interpolationLevels_card_pos u)]
  exact F.interpolationLevels_max_eq_one u hu
end BKAR.Forest
