-- Prove2me | solution 1 for BooleanIsoperimetry.card_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:13.966673+00:00
-- url     : https://prove2.me/submissions/56ceee84-bd84-40c9-8a18-714c8c41f592

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
public import Theorems.Thm_BooleanIsoperimetry_embed1_injective
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N b : ℕ} (hb : b ≤ 2 ^ N) :
    ((simplicialInitSeg N b).image embed1).card = b := by
  rw [Finset.card_image_of_injective _ embed1_injective, card_simplicialInitSeg, min_eq_left hb]
end BooleanIsoperimetry
