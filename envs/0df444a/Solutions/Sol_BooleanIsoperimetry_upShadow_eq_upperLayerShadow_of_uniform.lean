-- Prove2me | solution 1 for BooleanIsoperimetry.upShadow_eq_upperLayerShadow_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:29.161841+00:00
-- url     : https://prove2.me/submissions/3e257d30-ca7b-49b3-bc34-57402b49c0d4

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    Finset.upShadow A = upperLayerShadow N r A := by
  ext y
  simp only [upperLayerShadow, Finset.mem_filter]
  constructor
  · intro hy
    refine ⟨hy, ?_⟩
    rw [Finset.mem_upShadow_iff_exists_mem_card_add_one] at hy
    rcases hy with ⟨x, hxA, _hxy, hcard⟩
    rw [hA x hxA] at hcard
    exact hcard
  · exact And.left
end BooleanIsoperimetry
