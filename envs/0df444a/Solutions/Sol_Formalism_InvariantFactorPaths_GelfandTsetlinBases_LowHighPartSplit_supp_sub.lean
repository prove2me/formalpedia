-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.supp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:51.738995+00:00
-- url     : https://prove2.me/submissions/850b54d8-20c2-4200-97b9-8491c22530db

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_coeff_key
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_wExp_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_wExp_high
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_Gc_low
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_high_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_decomp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_gen_mem_supp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}
variable {k : Type*} [Field k] (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
theorem _root_.solution {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (last : Bool) (G : MvPolynomial (ℕ × Fin n) k)
    {β : ℕ × Fin n →₀ ℕ} (hβ : β ∈ G.support.image (highP i)) :
    (genAct (ζ := Empty) k isVec S last (rename Sum.inl (Gc i G β))).coeff.support ⊆
      (genAct (ζ := Empty) k isVec S last (rename Sum.inl G)).coeff.support := by
  intro j hj
  rw [gen_mem_supp] at hj ⊢
  obtain ⟨e, he, rfl⟩ := hj
  refine ⟨e + β.mapDomain Sum.inl, ?_, ?_⟩
  · rw [← Psi_apply] at he ⊢
    rw [Psi_decomp isVec S hS G]
    refine coeff_key (loSet n S) (G.support.image (highP i)) (fun γ => Psi isVec S (Gc i G γ))
      (fun γ => γ.mapDomain Sum.inl) (fun γ _ => Psi_Gc_low isVec S hS G γ) ?_
      (fun γ _ δ _ h => Finsupp.mapDomain_injective Sum.inl_injective h) hβ he
    intro γ hγ x hx
    obtain ⟨j', a, hj', rfl⟩ := hx
    rw [Finsupp.mapDomain_apply Sum.inl_injective]
    exact high_zero S hS hγ j' a hj'
  · rw [wExp_add, wExp_high isVec S last (high_zero S hS hβ), add_zero]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
