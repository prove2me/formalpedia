-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psiPath_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:46:37.158663+00:00
-- url     : https://prove2.me/submissions/33577253-13fb-481c-9cef-1495ccc535e8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_pathWord_congr

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) {μ μ' : ℕ → Fin n → ℤ} {N : ℕ}
    (h : ∀ i ≤ N, μ i = μ' i) (I : ℤ → Finset (Fin n)) :
    psiPath R isVec μ N I = psiPath R isVec μ' N I := by
  unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath
  exact finprod_congr fun c => by rw [pathWord_congr isVec μ μ' c _ N h]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
