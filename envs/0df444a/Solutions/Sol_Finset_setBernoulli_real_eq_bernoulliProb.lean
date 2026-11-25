-- Prove2me | solution 1 for Finset.setBernoulli_real_eq_bernoulliProb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:22.156437+00:00
-- url     : https://prove2.me/submissions/97e4b61c-617c-4bd6-8a0a-35ec4e93b109

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open Finset
variable {α : Type*} [DecidableEq α] [Countable α]
namespace Finset
theorem _root_.solution (U : Finset α) (p : I) {S : Set (Set α)}
    {Q : Finset α → Prop} [DecidablePred Q] (hQ : ∀ A ⊆ U, (A : Set α) ∈ S ↔ Q A) :
    setBer((U : Set α), p).real S = U.bernoulliProb p Q := by
  have hS : {s ∈ S | s ⊆ (U : Set α)} = ⋃ A ∈ U.powerset.filter Q, {(A : Set α)} := by
    ext s
    simp only [Set.mem_sep_iff, Set.mem_iUnion, Set.mem_singleton_iff, mem_filter, mem_powerset,
      exists_prop]
    constructor
    · rintro ⟨hs, hsU⟩
      lift s to Finset α using (U.finite_toSet.subset hsU)
      exact ⟨s, ⟨coe_subset.mp hsU, (hQ s (coe_subset.mp hsU)).mp hs⟩, rfl⟩
    · rintro ⟨A, ⟨hAU, hA⟩, rfl⟩
      exact ⟨(hQ A hAU).mpr hA, coe_subset.mpr hAU⟩
  rw [measureReal_def, setBernoulli_apply_eq_apply_subsets, ← measureReal_def, hS,
    measureReal_biUnion_finset (fun A _ B _ hAB => by simpa using hAB)
      (fun _ _ => measurableSet_singleton _), bernoulliProb]
  refine sum_congr rfl fun A hA => ?_
  have hAU := mem_powerset.mp (mem_filter.mp hA).1
  rw [setBernoulli_real_singleton p (coe_subset.mpr hAU) U.finite_toSet, ← coe_sdiff,
    Set.ncard_coe_finset, Set.ncard_coe_finset, bernoulliWeight]
end Finset
