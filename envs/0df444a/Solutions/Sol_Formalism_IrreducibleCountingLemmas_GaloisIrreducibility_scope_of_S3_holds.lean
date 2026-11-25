-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.scope_of_S3_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:22.838508+00:00
-- url     : https://prove2.me/submissions/98c6c314-508a-4120-95fb-26f7d2ccb970

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
theorem _root_.solution : CommutesWithIdempotents := by
  intro R V _ _ _ MM a eps pr hMM hae hap
  have hcomm : ∀ f : V →ₗ[R] V, a ∘ₗ f = f ∘ₗ a → ∀ y, a (f y) = f (a y) := by
    intro f hf y
    have := LinearMap.congr_fun hf y
    simpa using this
  have hrange : ∀ f : V →ₗ[R] V, a ∘ₗ f = f ∘ₗ a →
      ∀ x ∈ LinearMap.range f, a x ∈ LinearMap.range f := by
    intro f hf x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨a y, (hcomm f hf y).symm⟩
  have h1 : ∀ x ∈ MM ⊓ LinearMap.range eps, a x ∈ MM ⊓ LinearMap.range eps := by
    intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    exact ⟨hMM x hx.1, hrange eps hae x hx.2⟩
  refine ⟨h1, ?_, ?_⟩
  · intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    exact ⟨h1 x hx.1, hrange pr hap x hx.2⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨a z, h1 z hz, (hcomm pr hap z).symm⟩
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
