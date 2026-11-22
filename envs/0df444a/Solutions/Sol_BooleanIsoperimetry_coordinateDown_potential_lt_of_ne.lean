-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_potential_lt_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:39.165953+00:00
-- url     : https://prove2.me/submissions/34a46fe1-4c1c-475b-88d3-bc1fc6648804

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_simplicialLt_erase_self
public import Theorems.Thm_BooleanIsoperimetry_downMap_rank_le
public import Theorems.Thm_BooleanIsoperimetry_downMap_injOn
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_eq_image
public import Theorems.Thm_BooleanIsoperimetry_exists_downMap_ne_of_ne
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N))
    (hne : coordinateDown i A ≠ A) :
    compressionPotential (coordinateDown i A) < compressionPotential A := by
  unfold compressionPotential
  rw [coordinateDown_eq_image, Finset.sum_image (fun x hx y hy h => downMap_injOn i A hx hy h)]
  obtain ⟨x, hx, hxne⟩ := exists_downMap_ne_of_ne i A hne
  refine Finset.sum_lt_sum (fun x _ => downMap_rank_le i A x) ⟨x, hx, ?_⟩
  unfold downMap at hxne ⊢
  split at hxne
  · next hc => rw [if_pos hc]; exact rank_strictMono (simplicialLt_erase_self hc.1)
  · next => exact absurd rfl hxne
end BooleanIsoperimetry
