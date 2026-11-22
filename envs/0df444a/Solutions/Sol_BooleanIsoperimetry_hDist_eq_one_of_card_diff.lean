-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_eq_one_of_card_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:19.538955+00:00
-- url     : https://prove2.me/submissions/c1386907-8344-4e3a-a6fd-5f30ca093fe4

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
theorem _root_.solution {N r : ℕ} {u x : Cube N} (hu : u.card = r)
    (hx : x.card = r + 1) (hd : hDist u x ≤ 1) :
    u ⊆ x ∧ (x \ u).card = 1 := by
  unfold hDist at hd
  have hsd : symmDiff u x = (u \ x) ∪ (x \ u) := by
    ext y
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  have hdisj : Disjoint (u \ x) (x \ u) := disjoint_sdiff_sdiff
  have hcard : (u \ x).card + (x \ u).card ≤ 1 := by
    rw [hsd, Finset.card_union_of_disjoint hdisj] at hd; exact hd
  have hkey : (x \ u).card + u.card = (u \ x).card + x.card := by
    have h1 : (x \ u).card + u.card = (x ∪ u).card := Finset.card_sdiff_add_card x u
    have h2 : (u \ x).card + x.card = (u ∪ x).card := Finset.card_sdiff_add_card u x
    rw [h1, h2, Finset.union_comm]
  rw [hu, hx] at hkey
  have hudiff : (u \ x).card = 0 := by omega
  have hsub : u ⊆ x := by
    rw [← Finset.sdiff_eq_empty_iff_subset, ← Finset.card_eq_zero]
    exact hudiff
  exact ⟨hsub, by omega⟩
end BooleanIsoperimetry
