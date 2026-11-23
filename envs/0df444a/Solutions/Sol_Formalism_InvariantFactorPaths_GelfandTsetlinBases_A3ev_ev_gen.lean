-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.ev_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:26.020978+00:00
-- url     : https://prove2.me/submissions/2e81094d-5fe6-4f0b-97b5-e791734abe98

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf

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
theorem _root_.solution (hEV : FactEV) (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    (∀ ν : Fin n → ℤ,
      weightedHomogeneousComponent (torusW isVec) ν
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) ≠ 0 →
      DomLe ν (μ N)) ∧
    weightedHomogeneousComponent (torusW isVec) (μ N)
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) =
      C (brk (genMat k n) (genMat k n)⁻¹ (μ N) I) *
        psiPath (GenField k n) isVec μ N (canIdx (μ N)) :=
  hEV (GenField k n) n N isVec B μ I (genU k n) hp hI
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
