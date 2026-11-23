-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sum_mul_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:42.217235+00:00
-- url     : https://prove2.me/submissions/cba33cc5-6588-480f-bfd8-8ba964cf70a2

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (s : Multiset ℕ) (N : ℕ) (h : ∀ d ∈ s, 1 ≤ d) (hs : s.sum = N) :
    ∑ d ∈ Finset.Icc 1 N, d * s.count d = N := by
  have hsub : s.toFinset ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Multiset.mem_toFinset] at hd
    have h2 := Multiset.le_sum_of_mem hd
    rw [hs] at h2
    exact Finset.mem_Icc.mpr ⟨h d hd, h2⟩
  rw [← Finset.sum_subset hsub]
  · conv_rhs => rw [← hs]
    rw [Finset.sum_multiset_count]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [smul_eq_mul, mul_comm]
  · intro d _ hd
    rw [Multiset.mem_toFinset] at hd
    rw [Multiset.count_eq_zero.mpr hd, mul_zero]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
