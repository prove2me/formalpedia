-- Prove2me | solution 1 for BooleanIsoperimetry.paired_coordinate_step_cost_nonincrease
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:57.174816+00:00
-- url     : https://prove2.me/submissions/df4f8681-0aec-4909-aabb-bf1d5f0670a6

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_neighborhood_card_le
public import Theorems.Thm_BooleanIsoperimetry_coordinateUp_neighborhood_card_le


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A B A' B' : Finset (Cube N)}
    {i : Fin N} (hA : IsCoordinateUp i A A') (hB : IsCoordinateDown i B B') :
    PairShadowCost N A' B' ≤ PairShadowCost N A B := by
  unfold PairShadowCost
  have hAcard : A'.card = A.card := hA.1
  have hBcard : B'.card = B.card := hB.1
  have hNA : (neighborhood 1 A').card ≤ (neighborhood 1 A).card :=
    coordinateUp_neighborhood_card_le hA
  have hNB : (neighborhood 1 B').card ≤ (neighborhood 1 B).card :=
    coordinateDown_neighborhood_card_le hB
  have h1 : max (neighborhood 1 A').card B'.card ≤ max (neighborhood 1 A).card B.card := by
    rw [hBcard]; exact max_le_max hNA le_rfl
  have h2 : max (neighborhood 1 B').card A'.card ≤ max (neighborhood 1 B).card A.card := by
    rw [hAcard]; exact max_le_max hNB le_rfl
  exact Nat.add_le_add h1 h2
end BooleanIsoperimetry
