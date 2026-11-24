-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.sum_succs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:18.591874+00:00
-- url     : https://prove2.me/submissions/d070b1b9-1b55-4ed2-b551-40677a33c779

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
theorem _root_.solution (hP : GTPieri) {n : ℕ} (v : Bool) (b : ℕ) (μ : Fin n → ℤ) (hμ : Antitone μ) :
    ∑ ν ∈ succs v b μ, dGT n ν = dGT n μ * (n + b - 1).choose b := by
  unfold succs
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hP n μ b hμ).2
  · simp only [↓reduceIte]; exact (hP n μ b hμ).1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
