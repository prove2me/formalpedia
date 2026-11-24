-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.Step.antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.944798+00:00
-- url     : https://prove2.me/submissions/b591b340-1f38-40ed-9177-1ee0b99eaad4

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
namespace Step
theorem _root_.solution {n : ℕ} {v : Bool} {b : ℕ} {μ ν : Fin n → ℤ} (h : Step v b μ ν) : Antitone ν := by
  unfold Step at h
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact antitone_lower h
  · simp only [↓reduceIte] at h; exact antitone_upper h
end Step
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count
