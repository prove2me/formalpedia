-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twisted_idempotent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:00:51.69597+00:00
-- url     : https://prove2.me/submissions/f66e9739-0596-4c6f-8de4-694068a5b880

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_twistedIdem_def
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_of_mul_twistedIdem
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sum_coef_twisted
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_twistedIdem_coeff
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_conj_char_inv
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_asAlgebraHom_twistedIdem
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
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : TwistedIdempotent := by
  intro G _ _ J χ
  classical
  have tw_lemma : ∀ g : G, (twistedIdem J χ).coeff g =
      if h : g ∈ J then (Nat.card J : ℂ)⁻¹ * (((χ ⟨g, h⟩)⁻¹ : ℂˣ) : ℂ) else 0 := by
    intro g
    rw [twistedIdem_coeff]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨g, h⟩]
      · simp
      · intro b _ hb
        have : (b : G) ≠ g := fun e => hb (Subtype.ext e)
        simp [this]
      · simp
    · apply Finset.sum_eq_zero
      intro u _
      have : (u : G) ≠ g := fun e => h (e ▸ u.2)
      simp [this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nth_rw 1 [twistedIdem_def]
    rw [Finset.sum_mul]
    simp_rw [smul_mul_assoc, of_mul_twistedIdem, smul_smul]
    rw [← Finset.sum_smul, sum_coef_twisted, one_smul]
  · intro g
    rw [tw_lemma, tw_lemma]
    by_cases hg : g ∈ J
    · have hg' : g⁻¹ ∈ J := J.inv_mem hg
      rw [dif_pos hg', dif_pos hg, map_mul, conj_char_inv]
      have e : (⟨g⁻¹, hg'⟩ : J) = (⟨g, hg⟩ : J)⁻¹ := rfl
      rw [e, map_inv, inv_inv]
      simp
    · have hg' : g⁻¹ ∉ J := fun h => hg (by simpa using J.inv_mem h)
      rw [dif_neg hg', dif_neg hg, map_zero]
  · rw [tw_lemma, dif_pos J.one_mem]
    have e : (⟨1, J.one_mem⟩ : J) = 1 := rfl
    rw [e, map_one, inv_one, Units.val_one, mul_one]
  · intro V _ _ ρ
    ext x
    constructor
    · rintro ⟨y, rfl⟩ u
      show ρ (u : G) (ρ.asAlgebraHom (twistedIdem J χ) y) =
        ((χ u : ℂˣ) : ℂ) • ρ.asAlgebraHom (twistedIdem J χ) y
      rw [← Representation.asAlgebraHom_of]
      change (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G (u : G)) * ρ.asAlgebraHom (twistedIdem J χ)) y = _
      rw [← map_mul, of_mul_twistedIdem, map_smul]
      rfl
    · intro hx
      refine ⟨x, ?_⟩
      rw [asAlgebraHom_twistedIdem]
      have hx' : ∀ u : J, ρ (u : G) x = ((χ u : ℂˣ) : ℂ) • x := hx
      simp_rw [hx', smul_smul]
      rw [← Finset.sum_smul, sum_coef_twisted, one_smul]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
