-- Prove2me | solution 1 for DeletionCode.OptimalRedundancy.main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:55:39.733728+00:00
-- url     : https://prove2.me/submissions/f6062a06-b2da-4209-aa52-d72cb8fa8e19

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_OptimalRedundancy_optimalRedundancy_le_code
import Theorems.Thm_DeletionCode_CodeExistence_main
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
namespace DeletionCode.OptimalRedundancy
theorem _root_.solution (t : ℕ) (ht : 2 ≤ t) :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      optimalRedundancy t n ≤
        ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
          (K : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) := by
  obtain ⟨K, hK⟩ := CodeExistence.main t ht
  refine ⟨K, ?_⟩
  filter_upwards [hK] with n hn
  obtain ⟨C, hC, hne, hbound⟩ := hn
  exact (optimalRedundancy_le_code t n C hC hne).trans hbound
end DeletionCode.OptimalRedundancy
