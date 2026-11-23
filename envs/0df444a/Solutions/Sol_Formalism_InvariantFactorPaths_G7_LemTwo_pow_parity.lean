-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.pow_parity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:45.937798+00:00
-- url     : https://prove2.me/submissions/87e32fc0-7959-4825-81aa-25feb0857dc9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (i j : ℕ) : p * (p ^ 2) ^ i ≠ (p ^ 2) ^ j := by
  intro h
  have e1 : p * (p ^ 2) ^ i = p ^ (2 * i + 1) := by ring
  have e2 : (p ^ 2) ^ j = p ^ (2 * j) := by ring
  rw [e1, e2] at h
  have := Nat.pow_right_injective hp h
  omega
end Formalism.InvariantFactorPaths.G7.LemTwo
