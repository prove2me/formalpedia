-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_binomPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:44.114739+00:00
-- url     : https://prove2.me/submissions/edd983b7-2252-4647-bb97-8ea9798e8b26

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r : ℕ} (hr : 1 ≤ r) :
    neighborhood 1 (simplicialInitSeg N (binomPrefix N r)) =
    simplicialInitSeg N (binomPrefix N (r + 1)) := by
  rw [neighborhood_initSeg_eq, H_binomPrefix N r hr]
end BooleanIsoperimetry
