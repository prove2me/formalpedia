-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ppowq_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:32.397307+00:00
-- url     : https://prove2.me/submissions/52f1b93f-7525-4982-ae28-9a6c21ab0dd1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {i j : ℕ} (h : p * (p ^ 2) ^ i = p * (p ^ 2) ^ j) : i = j := by
  have h' : (p ^ 2) ^ i = (p ^ 2) ^ j := Nat.eq_of_mul_eq_mul_left (by omega) h
  exact powq_inj hp h'
end Formalism.InvariantFactorPaths.G7
