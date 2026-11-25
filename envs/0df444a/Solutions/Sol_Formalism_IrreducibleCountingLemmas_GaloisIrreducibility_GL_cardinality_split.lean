-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GL_cardinality_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:15.895725+00:00
-- url     : https://prove2.me/submissions/d8fddfe6-e363-4f3d-99e8-be60a62b8cff

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
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : GLCardSplit := by
  intro K _ _ N
  rw [Matrix.card_GL_field]
  set q := Fintype.card K
  have e1 : ∀ i : Fin N, q ^ N - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (N - i) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ N := i.isLt.le
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hi]
  rw [Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]
  · rw [Fin.prod_univ_eq_prod_range (fun i => q ^ (N - i) - 1) N]
    have e2 : Finset.Icc 1 N = (Finset.range N).image (fun i => N - i) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨N - j, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    rw [e2, Finset.prod_image (fun a ha b hb h => by simp at ha hb h; omega)]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
