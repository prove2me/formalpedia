-- Prove2me | solution 1 for DeletionCode.OptimalRedundancy.optimalRedundancy_le_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:17:56.324962+00:00
-- url     : https://prove2.me/submissions/af558c73-1707-4f1d-ba2c-061ea9479f47

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_OptimalRedundancy_card_le_optimalCodeSize

set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
namespace DeletionCode.OptimalRedundancy
theorem _root_.solution (t n : ℕ) (C : Finset (Bits n))
    (hC : CodeSelection.Corrects t C) (hne : C.Nonempty) :
    optimalRedundancy t n ≤ RedundancyBounds.redundancy n C := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hbound : (C.card : ℝ) ≤ optimalCodeSize t n := by
    exact_mod_cast card_le_optimalCodeSize t n C hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hc hbound
  unfold optimalRedundancy RedundancyBounds.redundancy
  linarith
end DeletionCode.OptimalRedundancy
