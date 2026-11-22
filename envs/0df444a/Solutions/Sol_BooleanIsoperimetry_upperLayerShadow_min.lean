-- Prove2me | solution 1 for BooleanIsoperimetry.upperLayerShadow_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:56.392858+00:00
-- url     : https://prove2.me/submissions/6dd98916-3acb-44be-a87f-ebf615fb58f9

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
public import Theorems.Thm_BooleanIsoperimetry_layerInitSeg_card
public import Theorems.Thm_BooleanIsoperimetry_upperLayerShadow_card_eq_shadow_compls
public import Theorems.Thm_BooleanIsoperimetry_layerInitSeg_uniform
public import Theorems.Thm_BooleanIsoperimetry_card_le_choose_of_uniform
public import Theorems.Thm_BooleanIsoperimetry_layerInitSeg_compls_isInitSeg

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
    (upperLayerShadow N r (layerInitSeg N r A.card)).card ≤
      (upperLayerShadow N r A).card := by
  rw [upperLayerShadow_card_eq_shadow_compls layerInitSeg_uniform,
      upperLayerShadow_card_eq_shadow_compls hA]
  refine Finset.kruskal_katona (r := N - r) ?hA ?hcard ?hinit
  · intro x hx
    change x ∈ Aᶜˢ at hx
    rw [Finset.mem_compls] at hx
    rw [← compl_compl x, Finset.card_compl, hA xᶜ hx, Fintype.card_fin]
  · rw [Finset.card_compls, Finset.card_compls,
      layerInitSeg_card (card_le_choose_of_uniform hA)]
  · exact layerInitSeg_compls_isInitSeg (N := N) (r := r) (t := A.card)
      (card_le_choose_of_uniform hA)
end BooleanIsoperimetry
