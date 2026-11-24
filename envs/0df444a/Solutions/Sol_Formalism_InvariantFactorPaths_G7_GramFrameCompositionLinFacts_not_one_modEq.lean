-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.not_one_modEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:18.266326+00:00
-- url     : https://prove2.me/submissions/8eeb160a-7ae9-4825-9d23-0da529940645

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree

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
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) : ¬ 1 ≡ p [MOD p ^ 2 - 1] := by
  intro h
  have h1 : p ^ 2 - 1 ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).1 h
  have h2 := Nat.le_of_dvd (by omega) h1
  have h3 : p * 2 ≤ p ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_left p hp
  omega
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
