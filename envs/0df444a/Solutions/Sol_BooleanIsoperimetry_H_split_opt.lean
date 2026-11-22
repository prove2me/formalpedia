-- Prove2me | solution 1 for BooleanIsoperimetry.H_split_opt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:06:44.617155+00:00
-- url     : https://prove2.me/submissions/55e78511-2863-4828-8aa2-542f480670fc

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_macaulay_optimization
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split
public import Theorems.Thm_BooleanIsoperimetry_slice_card_eq_cascade


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    max (H n (slice0 (simplicialInitSeg (n + 1) (a + b))).card)
        (slice1 (simplicialInitSeg (n + 1) (a + b))).card +
    max (H n (slice1 (simplicialInitSeg (n + 1) (a + b))).card)
        (slice0 (simplicialInitSeg (n + 1) (a + b))).card
    ≤ max (H n a) b + max (H n b) a := by
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, _, _, _, h_split⟩ := exists_cascade_split n (a + b) hab
  have ⟨h0, h1⟩ := slice_card_eq_cascade h_split
  rw [h0, h1]
  exact macaulay_optimization ha hb h_split
end BooleanIsoperimetry
