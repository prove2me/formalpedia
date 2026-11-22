-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_card_eq_cascade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:21.150813+00:00
-- url     : https://prove2.me/submissions/48a80261-5275-465c-8d2b-343cb867c576

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_cascadeSlice1Value_le
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_card_le_rank
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_card_succ
public import Theorems.Thm_BooleanIsoperimetry_slice1_eq_filter
public import Theorems.Thm_BooleanIsoperimetry_cascade_pred_iff
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    (slice1 (simplicialInitSeg (n + 1) k)).card = cascadeSlice1Value n r t := by
  have ht : t ≤ Nat.choose (n + 1) r := h.2.1
  have hkeq : k = binomPrefix (n + 1) r + t := h.2.2.1
  have hset : slice1 (simplicialInitSeg (n + 1) k)
      = simplicialInitSeg n (cascadeSlice1Value n r t) := by
    rw [slice1_eq_filter]
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, simplicialInitSeg]
    rw [hkeq]
    have hlo := binomPrefix_card_le_rank w
    have hhi := rank_lt_binomPrefix_card_succ w
    have hiff := cascade_pred_iff (n := n) (r := r) (t := t)
      (c := w.card) (rho := rank w) ht hlo hhi
    simpa [cascadeSlice1Value] using hiff
  rw [hset, card_simplicialInitSeg, min_eq_left (cascadeSlice1Value_le h)]
end BooleanIsoperimetry
