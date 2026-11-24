-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.evC_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:10.271454+00:00
-- url     : https://prove2.me/submissions/a0cf2d47-c9c0-4c2e-ae99-4c4ca5f69886

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_map_psi

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
theorem _root_.solution (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (ν : Fin n → ℤ) (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    evC k n isVec ν (psiPath k isVec μ N I) =
      weightedHomogeneousComponent (torusW isVec) ν
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) := by
  rw [← map_psi (algebraMap k (GenField k n)) hp hI]
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
