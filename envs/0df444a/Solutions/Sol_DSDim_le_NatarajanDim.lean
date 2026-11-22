-- Prove2me | solution 1 for DSDim_le_NatarajanDim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:14.387808+00:00
-- url     : https://prove2.me/submissions/9a382e5d-411f-41a5-8cb8-1aaf67f7e748

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) (Y : Type v) [Nontrivial Y]
    (C : ConceptClass X Y) : DSDim X Y C ≤ NatarajanDim X Y C := by
  obtain ⟨y₀, y₁, hne⟩ := exists_pair_ne Y
  apply iSup₂_le
  intro S hDS
  have hNat : ∃ (f₀ f₁ : X → Y), (∀ x ∈ S, f₀ x ≠ f₁ x) ∧
      ∀ (h : X → Bool), ∃ c ∈ C, ∀ x ∈ S,
        c x = if h x then f₀ x else f₁ x := by
    refine ⟨fun _ => y₀, fun _ => y₁, fun _ _ => hne, fun h => ?_⟩
    simp_all
  exact le_iSup₂_of_le S hNat (le_refl _)
