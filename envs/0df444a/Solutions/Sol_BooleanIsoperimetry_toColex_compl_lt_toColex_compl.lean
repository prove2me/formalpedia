-- Prove2me | solution 1 for BooleanIsoperimetry.toColex_compl_lt_toColex_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:23.265845+00:00
-- url     : https://prove2.me/submissions/a9ad5d38-d8e0-4580-a301-61c4d9b7b3a0

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
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_compl_lt_cubeToNat_compl
public import Theorems.Thm_BooleanIsoperimetry_toColex_lt_iff_cubeToNat_lt

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
    toColex Aᶜ < toColex Bᶜ ↔ toColex B < toColex A := by
  rw [toColex_lt_iff_cubeToNat_lt, toColex_lt_iff_cubeToNat_lt]
  exact cubeToNat_compl_lt_cubeToNat_compl
end BooleanIsoperimetry
