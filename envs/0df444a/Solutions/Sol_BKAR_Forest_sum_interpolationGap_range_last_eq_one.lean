-- Prove2me | solution 1 for BKAR.Forest.sum_interpolationGap_range_last_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:17.353456+00:00
-- url     : https://prove2.me/submissions/69365041-ce44-4a42-aef8-808535fb348d

import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_BKAR_ThresholdComponents
import Definitions.Def_BKAR_ThresholdLayerCake
import Theorems.Thm_BKAR_Forest_interpolationLevel_last
import Theorems.Thm_BKAR_Forest_sum_interpolationGap_range_eq_interpolationLevel_of_zero

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
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        F.interpolationGap u i) = 1 := by
  have hlast :
      (F.interpolationLevels u).card - 1 <
        (F.interpolationLevels u).card :=
    Nat.sub_lt (F.interpolationLevels_card_pos u) Nat.zero_lt_one
  rw [F.sum_interpolationGap_range_eq_interpolationLevel_of_zero u hu hlast]
  exact F.interpolationLevel_last u hu
end BKAR.Forest
