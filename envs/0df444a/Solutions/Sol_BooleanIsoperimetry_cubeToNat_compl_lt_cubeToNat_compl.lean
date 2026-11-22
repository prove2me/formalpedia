-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_compl_lt_cubeToNat_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:06.692821+00:00
-- url     : https://prove2.me/submissions/c9c0418f-f3c4-4aa1-bb05-ce4a5e25725d

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
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_add_compl

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
    cubeToNat Aᶜ < cubeToNat Bᶜ ↔ cubeToNat B < cubeToNat A := by
  have hA := cubeToNat_add_compl A
  have hB := cubeToNat_add_compl B
  omega
end BooleanIsoperimetry
