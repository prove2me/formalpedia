-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_eq_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:13.922527+00:00
-- url     : https://prove2.me/submissions/f949f1d0-4440-49b6-97c4-665c26cf8504

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
theorem _root_.solution (N r : ℕ) :
    binomPrefix N r = (Finset.univ.filter (fun (x : Cube N) => x.card < r)).card := by
  unfold binomPrefix
  have h_disj : (Finset.univ.filter (fun (x : Cube N) => x.card < r)) =
      Finset.biUnion (Finset.range r) (fun i => Finset.powersetCard i Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    exact ⟨fun h => ⟨x.card, h, ⟨Finset.subset_univ x, rfl⟩⟩, fun ⟨i, hi, hpow⟩ => hpow.2 ▸ hi⟩
  rw [h_disj]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i hi j hj hneq
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rw [Finset.mem_powersetCard] at hx hy
    omega
end BooleanIsoperimetry
