-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.square_mass_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:00:50.74917+00:00
-- url     : https://prove2.me/submissions/279924fa-5b9c-4265-a221-199de18d19f8

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_degType
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_one_le_of_mem_degType
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_inv_pow_sum_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_squarefree_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : SqMassLower := by
  intro K _ _ N hN
  have hq : (1 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hw : ∀ c ∈ sqSet K N, ((Fintype.card K : ℝ) ^ N)⁻¹ ≤ sqWeight (monicOf c) := by
    intro c _
    rw [sqWeight_eq]
    have h := inv_pow_sum_le _ hq (degType (monicOf c)) (one_le_of_mem_degType _)
    rwa [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree] at h
  have h1 : ((sqSet K N).card : ℝ) * ((Fintype.card K : ℝ) ^ N)⁻¹ ≤
      ∑ c ∈ sqSet K N, sqWeight (monicOf c) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hw
  have h2 : Fintype.card K ^ N ≤ (sqSet K N).card + 2 * Fintype.card K ^ (N - 1) :=
    squarefree_count K N hN
  have h3 : (Fintype.card K : ℝ) ^ N ≤ ((sqSet K N).card : ℝ) + 2 * (Fintype.card K : ℝ) ^ (N - 1) := by
    exact_mod_cast h2
  refine le_trans ?_ h1
  have hpos : (0 : ℝ) < (Fintype.card K : ℝ) ^ N := by positivity
  have h5 : (Fintype.card K : ℝ) ^ N = (Fintype.card K : ℝ) ^ (N - 1) * (Fintype.card K : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h6 : (2 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ N
      = 2 * (Fintype.card K : ℝ) ^ (N - 1) := by
    rw [h5]; field_simp
  nlinarith [h3, h6]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
