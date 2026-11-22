-- Prove2me | solution 1 for BooleanIsoperimetry.embed0_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:22.421449+00:00
-- url     : https://prove2.me/submissions/2883f558-45ca-474f-ae1d-baf453ccc72e

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (x : Cube n) : (embed0 x).card = x.card := by
  unfold embed0
  exact Finset.card_image_of_injective _ (Fin.castSucc_injective n)
end BooleanIsoperimetry
