-- Prove2me | solution 1 for FiniteLP.fg_cone_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:08.464809+00:00
-- url     : https://prove2.me/submissions/f9d938a4-bf13-4d36-99c7-eecc9fbcb27b

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_FiniteLP_simplicial_cone_isClosed
public import Theorems.Thm_FiniteLP_conic_caratheodory
attribute [local simp] FiniteLP.toE_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
namespace FiniteLP
theorem _root_.solution {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) :
    IsClosed {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y} := by
  have hset : {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y}
      = ⋃ s : Finset κ, ⋃ (_ : LinearIndepOn ℝ v s),
          {y : EuclideanSpace ℝ ι |
            ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc0, rfl⟩
      obtain ⟨d, s, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory v c hc0
      exact ⟨s, hindep, d, hd0, hdoff, hsum⟩
    · rintro ⟨s, hindep, c, hc0, hcoff, rfl⟩
      refine ⟨c, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      intro k _ hks; rw [hcoff k hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun h => simplicial_cone_isClosed v s h
end FiniteLP
