-- Prove2me | solution 1 for DeletionCode.OptimalRedundancy.exists_optimal_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:22:20.848658+00:00
-- url     : https://prove2.me/submissions/159a150c-5785-4301-8aff-bc701c99c7cf

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_OptimalRedundancy_mem_correctingCodes
import Theorems.Thm_DeletionCode_OptimalRedundancy_correctingCodes_nonempty
import Theorems.Thm_DeletionCode_OptimalRedundancy_optimalCodeSize_pos
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
namespace DeletionCode.OptimalRedundancy
theorem _root_.solution (t n : ℕ) :
    ∃ C : Finset (Bits n), CodeSelection.Corrects t C ∧ C.Nonempty ∧
      C.card = optimalCodeSize t n := by
  obtain ⟨C, hC, hmax⟩ := Finset.exists_mem_eq_sup
    (correctingCodes t n) (correctingCodes_nonempty t n) Finset.card
  have heq : C.card = optimalCodeSize t n := hmax.symm
  refine ⟨C, (mem_correctingCodes t n C).mp hC, ?_, heq⟩
  apply Finset.card_pos.mp
  rw [heq]
  exact optimalCodeSize_pos t n
end DeletionCode.OptimalRedundancy
