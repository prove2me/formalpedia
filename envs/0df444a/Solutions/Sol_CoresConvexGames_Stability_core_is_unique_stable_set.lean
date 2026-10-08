-- Prove2me | solution 1 for CoresConvexGames.Stability.core_is_unique_stable_set
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:41:54.888602+00:00
-- url     : https://prove2.me/submissions/5786311f-7620-4c29-bcf1-d2d48d18d048

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsFeasible
import Definitions.Def_CoresConvexGames_Stability_Dominates
import Definitions.Def_CoresConvexGames_Stability_IsStableSet
import Theorems.Thm_CoresConvexGames_Stability_dominated_by_core_of_not_mem_core

set_option autoImplicit false

open scoped BigOperators

namespace ShapleyStableProof

open Supermodularity.Cooperative CoresConvexGames.Stability

lemma core_not_dominated {n : ℕ} (f : Finset (Fin n) → ℝ)
    (b : Fin n → ℝ) (hb : b ∈ Core Finset.univ f) (a : Fin n → ℝ) :
    ¬ Dominates f a b := by
  rintro ⟨S, hS, ha, hab⟩
  have hsum : (∑ i ∈ S, b i) < ∑ i ∈ S, a i :=
    Finset.sum_lt_sum_of_nonempty hS hab
  have hbS := hb.2 S (Finset.subset_univ S)
  linarith

lemma stable_and_unique_of_external {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hext : ∀ b : Fin n → ℝ, IsFeasible f b → b ∉ Core Finset.univ f →
      ∃ a ∈ Core Finset.univ f, Dominates f a b) :
    IsStableSet f (Core Finset.univ f) ∧
      ∀ V : Set (Fin n → ℝ), IsStableSet f V → V = Core Finset.univ f := by
  have hfeas : ∀ b ∈ Core Finset.univ f, IsFeasible f b :=
    fun b hb => hb.1.le
  have hstab : IsStableSet f (Core Finset.univ f) := by
    refine ⟨hfeas, ?_⟩
    intro b hb
    constructor
    · rintro hbc ⟨a, _, hab⟩
      exact core_not_dominated f b hbc a hab
    · intro hnot
      by_contra hbc
      exact hnot (hext b hb hbc)
  refine ⟨hstab, ?_⟩
  intro V hV
  have hCV : Core Finset.univ f ⊆ V := by
    intro b hb
    apply (hV.2 b (hfeas b hb)).2
    rintro ⟨a, _, hab⟩
    exact core_not_dominated f b hb a hab
  apply Set.Subset.antisymm ?_ hCV
  intro b hb
  by_contra hbc
  obtain ⟨a, ha, hab⟩ := hext b (hV.1 b hb) hbc
  exact (hV.2 b (hV.1 b hb)).1 hb ⟨a, hCV ha, hab⟩

end ShapleyStableProof

open Supermodularity.Cooperative CoresConvexGames.Stability ShapleyStableProof in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f) :
    IsStableSet f (Core Finset.univ f) ∧
      ∀ V : Set (Fin n → ℝ), IsStableSet f V → V = Core Finset.univ f :=
  stable_and_unique_of_external f (dominated_by_core_of_not_mem_core f hf)
