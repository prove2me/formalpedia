-- Prove2me | solution 1 for BooleanIsoperimetry.upShadow_subset_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:18.885207+00:00
-- url     : https://prove2.me/submissions/1570ed47-0612-4933-aff1-250fd5227810

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
theorem _root_.solution {N r : ℕ} (A : Finset (Cube N)) (_ : ∀ x ∈ A, x.card = r) :
    Finset.upShadow A ⊆ neighborhood 1 A := by
  intro x hx
  rw [Finset.mem_upShadow_iff] at hx
  obtain ⟨u, hu, a, ha, hins⟩ := hx
  rw [mem_neighborhood_iff]
  refine ⟨u, hu, ?_⟩
  have hone : hDist u x = 1 := by
    unfold hDist
    have hsd : symmDiff u x = {a} := by
      rw [← hins]
      ext y
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨hyu, hni⟩ | ⟨hyi, hnu⟩)
        · exact absurd (Or.inr hyu) hni
        · rcases hyi with h | h
          · exact h
          · exact absurd h hnu
      · rintro rfl
        exact Or.inr ⟨Or.inl rfl, ha⟩
    rw [hsd]; simp
  omega
end BooleanIsoperimetry
