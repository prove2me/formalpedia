-- Prove2me | solution 1 for Champernowne.sum_countOccurrences_allWords_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:31.535871+00:00
-- url     : https://prove2.me/submissions/e945d0c5-863a-4200-abc1-1ed53647fbd8

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
public import Theorems.Thm_Champernowne_countOccurrences_eq_card_filter_range
public import Theorems.Thm_Champernowne_mem_allWords

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b k : ℕ) (l : List ℕ) :
    ∑ v ∈ allWords b k, countOccurrences v l ≤ l.length + 1 := by
  have hdisj : ∀ v₁ ∈ allWords b k, ∀ v₂ ∈ allWords b k, v₁ ≠ v₂ →
      Disjoint
        ((Finset.range (l.length + 1)).filter (fun j => v₁.isPrefixOf (l.drop j)))
        ((Finset.range (l.length + 1)).filter (fun j => v₂.isPrefixOf (l.drop j))) := by
    intro v₁ h₁ v₂ h₂ hne
    rw [Finset.disjoint_left]
    rintro j hj₁ hj₂
    have hp₁ := List.isPrefixOf_iff_prefix.mp (Finset.mem_filter.mp hj₁).2
    have hp₂ := List.isPrefixOf_iff_prefix.mp (Finset.mem_filter.mp hj₂).2
    have hlen₁ := (mem_allWords.mp h₁).1
    have hlen₂ := (mem_allWords.mp h₂).1
    apply hne
    calc v₁ = (l.drop j).take v₁.length := List.prefix_iff_eq_take.mp hp₁
    _ = (l.drop j).take v₂.length := by rw [hlen₁, hlen₂]
    _ = v₂ := (List.prefix_iff_eq_take.mp hp₂).symm
  calc ∑ v ∈ allWords b k, countOccurrences v l
      = ∑ v ∈ allWords b k,
          ((Finset.range (l.length + 1)).filter
            (fun j => v.isPrefixOf (l.drop j))).card :=
        Finset.sum_congr rfl fun v _ => countOccurrences_eq_card_filter_range v l
  _ = ((allWords b k).biUnion fun v =>
        (Finset.range (l.length + 1)).filter
          (fun j => v.isPrefixOf (l.drop j))).card :=
        (Finset.card_biUnion hdisj).symm
  _ ≤ (Finset.range (l.length + 1)).card :=
        Finset.card_le_card
          (Finset.biUnion_subset.mpr fun v _ => Finset.filter_subset _ _)
  _ = l.length + 1 := Finset.card_range _
end Champernowne
