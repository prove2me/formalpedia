-- Prove2me | solution 1 for BooleanIsoperimetry.initial_segment_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:07:53.709807+00:00
-- url     : https://prove2.me/submissions/669bda28-8f02-42b7-a9c9-a4519a720976

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
public import Theorems.Thm_BooleanIsoperimetry_H_inequality
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_card_initSeg_union
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (k0 k1 : ℕ) (hk0 : k0 ≤ 2 ^ n) (hk1 : k1 ≤ 2 ^ n) :
    (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card ≤
    (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
    (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by
  change H (n + 1) (k0 + k1) ≤ _
  rw [neighborhood_initSeg_eq, neighborhood_initSeg_eq]
  rw [card_initSeg_union (H_le_cube n k0) hk1, card_initSeg_union (H_le_cube n k1) hk0]
  exact H_inequality n k0 k1 hk0 hk1
end BooleanIsoperimetry
