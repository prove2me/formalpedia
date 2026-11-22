-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_q_le_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:36.3748+00:00
-- url     : https://prove2.me/submissions/87f472a9-99c0-4308-918b-6e618755ff24

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pred_add_choosePred

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k p q : ℕ} (h : CascadeSplit n k p q) : q ≤ p := by
  obtain ⟨r, t, _, hp, hq⟩ := h
  have hadd := binomPrefix_pred_add_choosePred n r
  rw [hp, hq]
  unfold cascadeSlice0Value cascadeSlice1Value
  omega
end BooleanIsoperimetry
