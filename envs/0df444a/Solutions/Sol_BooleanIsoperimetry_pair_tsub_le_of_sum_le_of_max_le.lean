-- Prove2me | solution 1 for BooleanIsoperimetry.pair_tsub_le_of_sum_le_of_max_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:17.158006+00:00
-- url     : https://prove2.me/submissions/6829690d-322b-4101-896d-528151b75cb2

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows

set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution {a b a' b' c : ℕ}
    (hsum : a + b ≤ a' + b') (hmax : max a b ≤ max a' b') :
    (a - c) + (b - c) ≤ (a' - c) + (b' - c) := by
  omega
end BooleanIsoperimetry
