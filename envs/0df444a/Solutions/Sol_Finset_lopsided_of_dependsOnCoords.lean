-- Prove2me | solution 1 for Finset.lopsided_of_dependsOnCoords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:17.007245+00:00
-- url     : https://prove2.me/submissions/4d695ad9-ae08-4496-be19-7fcecea4b6fa

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_bernoulliProb_and


set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]
namespace Finset
theorem _root_.solution [DecidableEq ι] {I : Finset ι} {T : ι → Finset α}
    (hT : ∀ i ∈ I, T i ⊆ U)
    (hE : ∀ i ∈ I, DependsOnCoords (E i) (T i)) :
    Lopsided U p I E fun i => I.filter fun j => j ≠ i ∧ ¬Disjoint (T i) (T j) := by
  intro i hi S hS hSΓ hiS
  refine (bernoulliProb_and (hT i hi) (biUnion_subset.mpr fun j hj => hT j (hS hj))
    ?_ (hE i hi) ?_).le
  · refine (disjoint_biUnion_right _ _ _).mpr fun j hj => ?_
    by_contra hij
    exact disjoint_left.mp hSΓ hj (mem_filter.mpr ⟨hS hj, fun h => hiS (h ▸ hj), hij⟩)
  · intro A B hAB
    refine forall₂_congr fun j hj => not_congr (hE j (hS hj) A B ?_)
    have hsub : T j ⊆ S.biUnion T := subset_biUnion_of_mem T hj
    rw [← inter_eq_right.mpr hsub, ← inter_assoc, ← inter_assoc, hAB]
end Finset
