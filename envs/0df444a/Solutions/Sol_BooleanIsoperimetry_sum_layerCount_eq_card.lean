-- Prove2me | solution 1 for BooleanIsoperimetry.sum_layerCount_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:34.444602+00:00
-- url     : https://prove2.me/submissions/b742368e-46a6-4fcf-ac29-d46ddd6427a8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset
namespace BooleanIsoperimetry
theorem _root_.solution (N : ℕ) (A : Finset (Cube N)) :
    ∑ r ∈ Finset.range (N + 2), layerCount N r A = A.card := by
  unfold layerCount layerPart
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := fun x : Cube N => x.card)
    (t := Finset.range (N + 2))
    (fun x _ => by
      simp only [Finset.coe_range, Set.mem_Iio]
      have hle : x.card ≤ N := by
        have := Finset.card_le_univ x
        simpa [Fintype.card_fin] using this
      omega)
end BooleanIsoperimetry
