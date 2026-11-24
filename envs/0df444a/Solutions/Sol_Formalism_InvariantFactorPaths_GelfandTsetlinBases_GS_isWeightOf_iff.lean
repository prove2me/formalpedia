-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.isWeightOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:02.176786+00:00
-- url     : https://prove2.me/submissions/76824c4e-43e9-4361-b3a9-9c01b8a08474

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_mem_genSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_hasWeight_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_whc_mem

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (G : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) :
    IsWeightOf isVec S (genSpace isVec S G) ν ↔ ∃ e ∈ (rho isVec S G).support, wt isVec S e = ν := by
  classical
  constructor
  · rintro ⟨f, hf, hne, hw⟩
    obtain ⟨ℓ, rfl⟩ := (mem_genSpace isVec S).mp hf
    obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hne
    refine ⟨e, ?_, (hasWeight_iff isVec S _ _).mp hw he⟩
    rw [mem_support_iff]
    intro h0
    rw [coeff_slc, h0, map_zero] at he
    exact he rfl
  · rintro ⟨e, he, rfl⟩
    rw [mem_support_iff] at he
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : UR k n →ₗ[k] k, ℓ (coeff e (rho isVec S G)) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact he ((Module.forall_dual_apply_eq_zero_iff k _).mp hc)
    refine ⟨weightedHomogeneousComponent (wV isVec S) (wt isVec S e) (slc ℓ (rho isVec S G)),
      whc_mem isVec S ((mem_genSpace isVec S).mpr ⟨ℓ, rfl⟩) _, ?_,
      (hasWeight_iff isVec S _ _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩
    refine MvPolynomial.ne_zero_iff.mpr ⟨e, ?_⟩
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_slc]
    exact hℓ
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
