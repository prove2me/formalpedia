-- Prove2me | solution 1 for BooleanIsoperimetry.toColex_lt_iff_cubeToNat_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:11.13283+00:00
-- url     : https://prove2.me/submissions/ba06d19a-0e91-449e-85aa-7c2ad1019004

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

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A B : Finset (Fin N)} :
    toColex A < toColex B ↔ cubeToNat A < cubeToNat B := by
  have h_image_A : cubeToNat A = ∑ i ∈ A.image (fun i : Fin N => (i:ℕ)), 2^i := by
    unfold cubeToNat
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact Fin.val_injective hxy
  have h_image_B : cubeToNat B = ∑ i ∈ B.image (fun i : Fin N => (i:ℕ)), 2^i := by
    unfold cubeToNat
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact Fin.val_injective hxy
  rw [h_image_A, h_image_B]
  rw [Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex (by norm_num)]
  rw [Finset.Colex.toColex_image_lt_toColex_image]
  · intro x y hxy; exact hxy
end BooleanIsoperimetry
