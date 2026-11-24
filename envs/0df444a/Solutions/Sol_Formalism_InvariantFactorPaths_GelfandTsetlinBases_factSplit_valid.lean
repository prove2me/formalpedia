-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.factSplit_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:06.471291+00:00
-- url     : https://prove2.me/submissions/c84575ea-95cd-4bd7-b77c-1d450df58855

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_lowerUnipotent_symm_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_highPart_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_mem_polB
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_decomp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_supp_sub

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
open LowHighPartSplit
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : FactSplit := by
  intro k _ n N i isVec B θ M G hiN hG
  refine ⟨G.support.image (highP i), Gc i G, ?_, ?_, decomp i G, ?_⟩
  · intro β hβ j
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hβ
    have h := (mem_polB.mp hG) e he j
    simp only [highPart_apply]
    by_cases hji : j < i
    · simp only [if_pos hji, Finset.sum_const_zero]
      rw [if_neg (by omega)]
    · simp only [if_neg hji]
      rw [h]
      by_cases hjN : j < N
      · rw [if_pos hjN, if_pos ⟨by omega, hjN⟩]
      · rw [if_neg hjN, if_neg (by omega)]
  · intro β hβ
    rw [mem_polB]
    intro e he j
    have he2 : e ∈ (∑ e ∈ G.support.filter (fun e => highP i e = β),
        monomial (lowP i e) (coeff e G)).support := he
    have hsub := Finset.mem_of_subset support_sum he2
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hsub
    obtain ⟨e', ⟨he', -⟩, hmem⟩ := hsub
    rw [Finset.mem_singleton.mp (support_monomial_subset hmem)]
    simp only [lowerUnipotent_symm_apply]
    have h := (mem_polB.mp hG) e' he' j
    by_cases hji : j < i
    · simp only [if_pos hji]
      rw [h, if_pos (by omega : j < N)]
    · simp only [if_neg hji, Finset.sum_const_zero]
  · intro hgood β hβ
    obtain ⟨h1, h2⟩ := hgood
    have hS : ∀ j, j ∈ {j : ℕ | j < i} ↔ j < i := fun j => Iff.rfl
    exact ⟨fun t ht => le_trans (h1 t ht) (Finset.min_mono (supp_sub isVec {j : ℕ | j < i} hS true G hβ)),
      fun t ht => le_trans (Finset.max_mono (supp_sub isVec {j : ℕ | j < i} hS false G hβ)) (h2 t ht)⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
