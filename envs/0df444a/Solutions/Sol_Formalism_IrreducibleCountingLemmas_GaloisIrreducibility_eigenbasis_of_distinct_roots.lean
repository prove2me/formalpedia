-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eigenbasis_of_distinct_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:14:59.170034+00:00
-- url     : https://prove2.me/submissions/9db8ad91-ba0d-4a81-8c9d-0baf77df50c7

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
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : EigenbasisOfDistinctRoots := by
  intro k V ι _ _ _ _ _ t c hc hchar
  classical
  have hroot : ∀ i, t.HasEigenvalue (c i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  choose v hv using fun i => (hroot i).exists_hasEigenvector
  have hli : LinearIndependent k v := Module.End.eigenvectors_linearIndependent' t c hc v hv
  have hdeg : (∏ i, (X - C (c i))).natDegree = Fintype.card ι := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (c i))]
    simp
  have hcard : Fintype.card ι = Module.finrank k V := by
    rw [← hdeg, ← hchar, LinearMap.charpoly_natDegree]
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : Subsingleton V := Module.finrank_zero_iff.1 (by rw [← hcard]; simp)
    exact ⟨Module.Basis.empty V, fun i => isEmptyElim i⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact (hv i).apply_eq_smul
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
