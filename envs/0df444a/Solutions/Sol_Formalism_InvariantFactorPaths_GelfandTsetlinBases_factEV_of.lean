-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.factEV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:31.335724+00:00
-- url     : https://prove2.me/submissions/9d900330-6a99-4152-a6d8-e07e2660f60e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_exists_cols
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_psi_eq_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_brk_eq_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_act_psi
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_term_cases
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_term_hom
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_idxWeight_can
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isIndex_can
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_isIndex_can


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
open A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : IndexWeightsDominance → PsiWeight → FactEV := by
  intro hT hW L _ n N isVec B μ I g hp hI
  obtain ⟨F, hF⟩ := exists_cols hp
  have hanti : Antitone (μ N) := hp.2.1 N le_rfl
  have key : ∀ (ν : Fin n → ℤ) (p : ∀ c ∈ F, Finset (Fin n)),
      weightedHomogeneousComponent (torusW isVec) ν
        (term isVec μ N F (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) I
          (extF F p)) ≠ 0 →
      IsIndex (μ N) (extF F p) ∧ idxWeight (extF F p) = ν := by
    intro ν p hne
    rcases term_cases hF (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) hI
      (extF F p) (fun c hc => dif_neg hc) with h | h
    · refine ⟨h, ?_⟩
      by_contra hν
      exact hne ((term_hom hW hp hF _ _ I h).weightedHomogeneousComponent_ne ν (Ne.symm hν))
    · rw [h, map_zero] at hne
      exact absurd rfl hne
  rw [act_psi hF g hI]
  constructor
  · intro ν hne
    rw [map_sum] at hne
    obtain ⟨p, _, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨h1, h2⟩ := key ν p hp'
    rw [← h2]
    exact (hT n (μ N) _ hanti h1).1
  · rw [map_sum, Finset.sum_eq_single (fun c _ => canIdx (μ N) c)]
    · have hcan : extF F (fun c _ => canIdx (μ N) c) = canIdx (μ N) := by
        funext c
        unfold extF
        split_ifs with h
        · rfl
        · exact ((hF c h).2 _ (A1hw.isIndex_can _)).symm
      rw [hcan]
      have hh := term_hom hW hp hF (↑g : Matrix (Fin n) (Fin n) L)
        (↑g⁻¹ : Matrix (Fin n) (Fin n) L) I (A1hw.isIndex_can (μ N))
      rw [idxWeight_can hanti] at hh
      rw [hh.weightedHomogeneousComponent_same]
      unfold term
      rw [← psi_eq_prod L hF (A1hw.isIndex_can _), ← brk_eq_prod hF _ _ hI, mul_comm]
    · intro p _ hpne
      by_contra hne
      obtain ⟨h1, h2⟩ := key _ p hne
      apply hpne
      have h3 := (hT n (μ N) _ hanti h1).2 h2
      funext c hc
      have h4 := congrFun h3 c
      unfold extF at h4
      rw [dif_pos hc] at h4
      exact h4
    · intro h
      exact absurd (Finset.mem_pi.2 fun _ _ => Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
