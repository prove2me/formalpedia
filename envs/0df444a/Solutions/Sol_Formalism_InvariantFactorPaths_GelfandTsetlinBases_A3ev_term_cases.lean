-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.term_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.836851+00:00
-- url     : https://prove2.me/submissions/f7ddd2db-a915-40f1-8939-248ae997314d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_ne


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) (I' : ℤ → Finset (Fin n))
    (h0 : ∀ c ∉ F, I' c = ∅) :
    IsIndex (μ N) I' ∨ term isVec μ N F g gi I I' = 0 := by
  by_cases h : ∀ c ∈ F, (I' c).card = (I c).card
  · left
    intro c
    by_cases hc : c ∈ F
    · rw [h c hc]; exact hI c
    · rw [h0 c hc, ← (hF c hc).2 I hI]; exact hI c
  · right
    push Not at h
    obtain ⟨c, hc, hne⟩ := h
    have : ∏ c ∈ F, minorF (if 1 ≤ c then g else gi.transpose) (I' c) (I c) = 0 :=
      Finset.prod_eq_zero hc (minorF_ne _ (Ne.symm hne))
    unfold term
    rw [this, map_zero, mul_zero]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
