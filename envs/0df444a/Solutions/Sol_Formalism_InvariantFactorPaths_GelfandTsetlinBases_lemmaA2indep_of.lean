-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lemmaA2indep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:22.38461+00:00
-- url     : https://prove2.me/submissions/4172cc22-c1b3-466b-8685-0bf95ff441c1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_domLe_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_ev_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_evC_psi
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_fam_li

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
theorem _root_.solution : FactEV → FactBrk → LemmaA2indep := by
  intro hEV hBrk k _ n N isVec B
  classical
  rw [linearIndependent_iff']
  intro s a hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁s, hx₁⟩ := hcon
  have hT : (s.filter fun x => a x ≠ 0).Nonempty := ⟨x₁, Finset.mem_filter.2 ⟨hx₁s, hx₁⟩⟩
  obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image _
    (fun x : PathIdx n N isVec B => height (x.1.1 N)) hT
  rw [Finset.mem_filter] at hx₀
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, x₀.1.1 N = μ₀ := ⟨_, rfl⟩
  have hanti : Antitone μ₀ := hμ₀ ▸ x₀.2.1.2.1 N le_rfl
  have h1 := congrArg (evC k n isVec μ₀) hsum
  rw [map_sum, map_zero] at h1
  simp_rw [map_smul] at h1
  have h2 : ∑ x ∈ s.filter (fun x => x.1.1 N = μ₀), a x • fam k x = 0 := by
    have h3 := Finset.sum_filter_of_ne (s := s)
      (p := fun x : PathIdx n N isVec B => x.1.1 N = μ₀)
      (f := fun x => a x • evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2)) ?_
    · rw [← h1, ← h3]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_filter] at hx
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1, ← hx.2, (ev_gen hEV k x.2.1 x.2.2.2.1).2]
      unfold fam
      rw [smul_eq_C_mul]
    · intro x hx hne
      have ha : a x ≠ 0 := fun h => hne (by rw [h, zero_smul])
      have he : evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2) ≠ 0 :=
        fun h => hne (by rw [h, smul_zero])
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1] at he
      have hd : DomLe μ₀ (x.1.1 N) := (ev_gen hEV k x.2.1 x.2.2.2.1).1 μ₀ he
      refine domLe_eq hd ?_
      rw [← hμ₀]
      exact hmax x (Finset.mem_filter.2 ⟨hx, ha⟩)
  exact hx₀.2 (linearIndepOn_iff'.1 (fam_li hBrk k n N isVec B μ₀ hanti) _ a
    (fun x hx => (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2) h2 x₀
    (Finset.mem_filter.2 ⟨hx₀.1, hμ₀⟩))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
