-- Prove2me | solution 1 for BooleanIsoperimetry.card_embed0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:13.250427+00:00
-- url     : https://prove2.me/submissions/78340baf-4807-49d2-af72-147666348c2c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_embed0_injective
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a : ℕ} (ha : a ≤ 2 ^ N) :
    ((simplicialInitSeg N a).image embed0).card = a := by
  rw [Finset.card_image_of_injective _ embed0_injective, card_simplicialInitSeg, min_eq_left ha]
end BooleanIsoperimetry
