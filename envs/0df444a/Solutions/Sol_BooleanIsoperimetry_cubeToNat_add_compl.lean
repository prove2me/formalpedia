-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_add_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:29.741419+00:00
-- url     : https://prove2.me/submissions/aeaa42be-04ea-4c11-9f6f-84c30f0412c1

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
theorem _root_.solution {N : ℕ} (A : Finset (Fin N)) :
    cubeToNat A + cubeToNat Aᶜ = cubeToNat (Finset.univ : Cube N) := by
  unfold cubeToNat
  exact sum_add_sum_compl A (fun (i:Fin N) => 2^(i:ℕ))
end BooleanIsoperimetry
