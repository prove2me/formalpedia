-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.term_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.883824+00:00
-- url     : https://prove2.me/submissions/e390383a-a8d8-46b9-b99a-a9b21f805573

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_psi_eq_prod

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
theorem _root_.solution (hW : PsiWeight) {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} (hp : IsPath n isVec B μ N)
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    (I : ℤ → Finset (Fin n)) {I' : ℤ → Finset (Fin n)} (hI' : IsIndex (μ N) I') :
    IsWeightedHomogeneous (torusW isVec) (term isVec μ N F g gi I I') (idxWeight I') := by
  unfold term
  rw [← psi_eq_prod L hF hI', mul_comm]
  exact (hW L n N isVec B μ I' hp hI').C_mul _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
