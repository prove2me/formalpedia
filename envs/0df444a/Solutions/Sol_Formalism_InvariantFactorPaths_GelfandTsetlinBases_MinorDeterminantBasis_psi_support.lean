-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.psi_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:07.743317+00:00
-- url     : https://prove2.me/submissions/8c0c2396-3a0d-486b-b437-879fbc73188b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_pathProductDegrees

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace MinorDeterminantBasis
section Abstract
variable {σ X : Type} [Fintype X] [DecidableEq X]
end Abstract
private theorem weight_indicator_fst_eq_sum {n : ℕ} (i : ℕ) (d : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) d = ∑ a, d (i, a) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ =>
    rw [map_add, h₁, h₂]
    simp [Finset.sum_add_distrib]
  | single x k =>
    obtain ⟨j, b⟩ := x
    rw [Finsupp.weight_single]
    by_cases hj : j = i
    · subst hj
      simp [Finsupp.single_apply, Prod.ext_iff]
    · simp [Finsupp.single_apply, Prod.ext_iff, hj]
end MinorDeterminantBasis
open MinorDeterminantBasis
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
theorem _root_.solution (hr : PolBRank) {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    ∀ d ∈ (psiPath ℤ isVec μ N I).support, d ∈ expSet n N B := by
  intro d hd i
  rw [← weight_indicator_fst_eq_sum]
  exact (pathProductDegrees ℤ n N isVec B μ I hμ hI).2 i (mem_support_iff.mp hd)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
