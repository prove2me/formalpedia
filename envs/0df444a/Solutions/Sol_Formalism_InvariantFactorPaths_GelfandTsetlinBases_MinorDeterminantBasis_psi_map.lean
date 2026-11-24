-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.psi_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:05.144068+00:00
-- url     : https://prove2.me/submissions/ce02ace7-580a-4436-8ec9-6489259c1517

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_map_pathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_pathProductDegrees


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
theorem _root_.solution (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    psiPath R isVec μ N I = MvPolynomial.map (Int.castRingHom R) (psiPath ℤ isVec μ N I) := by
  have hfin := (pathProductDegrees ℤ n N isVec B μ I hμ hI).1
  have h := (MvPolynomial.map (Int.castRingHom R) :
    MvPolynomial (ℕ × Fin n) ℤ →+* MvPolynomial (ℕ × Fin n) R).toMonoidHom.map_finprod hfin
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h
  unfold psiPath
  rw [h]
  congr 1
  funext c
  rw [A1hw.map_pathWord]
  simp [map_X]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
