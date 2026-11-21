-- Prove2me | solution 1 for Champernowne.length_champBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:37:43.799145+00:00
-- url     : https://prove2.me/submissions/729d727d-319e-4802-8ea8-ec576fcf5c1b

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b N : ℕ) :
    (champBlocks b N).length
      = ∑ n ∈ Finset.Ico 1 (N + 1), (bigDigits b n).length := by
  induction N with
  | zero => simp [champBlocks]
  | succ n ih =>
    rw [champBlocks_succ, List.length_append, ih]
    exact (Finset.sum_Ico_succ_top (show 1 ≤ n + 1 by omega) _).symm
end Champernowne
