-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLt_erase_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:45.990026+00:00
-- url     : https://prove2.me/submissions/2861f50e-e656-417d-b017-bbed9872feea

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {x : Cube N} (hi : i ∈ x) :
    simplicialLt (x.erase i) x := by
  have hpos : 0 < x.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hcard : (x.erase i).card = x.card - 1 := Finset.card_erase_of_mem hi
  refine ⟨Or.inl ?_, ?_⟩
  · rw [hcard]; omega
  · rintro (h | ⟨h, _⟩) <;> · rw [hcard] at h; omega
end BooleanIsoperimetry
