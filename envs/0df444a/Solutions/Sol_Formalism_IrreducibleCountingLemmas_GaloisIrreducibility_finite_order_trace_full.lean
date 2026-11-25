-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.finite_order_trace_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:13:51.519237+00:00
-- url     : https://prove2.me/submissions/3c90804c-741b-442f-98e1-16796d854de5

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_end_eq_one_of_trace
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
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
theorem _root_.solution : FiniteOrderTraceFull := by
  intro K _ φ n m γ hm hγ htr
  classical
  set γ' : Matrix (Fin n) (Fin n) ℂ := γ.map φ with hγ'
  have h1 : γ' ^ m = 1 := by
    rw [hγ', ← Matrix.map_pow, hγ, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have h2 : γ'.trace = (n : ℂ) := by
    have : γ'.trace = φ γ.trace := by simp [Matrix.trace, hγ', map_sum]
    rw [this, htr, map_natCast]
  have hs : (Matrix.toLinAlgEquiv' γ') ^ m = 1 := by rw [← map_pow, h1, map_one]
  have hts : LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' γ') =
      (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    rw [Module.finrank_fin_fun]
    exact (Matrix.trace_toLin'_eq γ').trans h2
  have h3 := end_eq_one_of_trace _ m hm hs hts
  have h4 : γ' = 1 := by
    have := congrArg (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).symm h3
    simpa using this
  apply Matrix.map_injective φ.injective
  show γ.map φ = (1 : Matrix (Fin n) (Fin n) K).map φ
  rw [← hγ', h4, Matrix.map_one φ (map_zero φ) (map_one φ)]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
