-- Prove2me | solution 1 for Champernowne.sum_le_countOccurrences_champBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:21.939071+00:00
-- url     : https://prove2.me/submissions/f652c309-3050-4a41-b198-ae0cfa699c6d

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
public import Theorems.Thm_Champernowne_countOccurrences_nil
public import Theorems.Thm_Champernowne_add_countOccurrences_le_append

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} {w : List ℕ}
    (hw : w ≠ []) (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 (N + 1), countOccurrences w (bigDigits b n)
      ≤ countOccurrences w (champBlocks b N) := by
  induction N with
  | zero => simp [champBlocks, countOccurrences_nil hw]
  | succ n ih =>
    rw [champBlocks_succ, Finset.sum_Ico_succ_top (by omega)]
    calc (∑ k ∈ Finset.Ico 1 (n + 1), countOccurrences w (bigDigits b k))
          + countOccurrences w (bigDigits b (n + 1))
        ≤ countOccurrences w (champBlocks b n)
          + countOccurrences w (bigDigits b (n + 1)) :=
          Nat.add_le_add_right ih _
    _ ≤ _ := add_countOccurrences_le_append hw _ _
end Champernowne
