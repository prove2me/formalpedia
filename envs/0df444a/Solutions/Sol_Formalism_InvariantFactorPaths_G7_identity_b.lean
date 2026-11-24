-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.identity_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:39.426313+00:00
-- url     : https://prove2.me/submissions/86648bb8-fd00-4f05-939c-521c12ba8136

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_AA_eq

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
theorem _root_.solution : IdentityB := by
  intro K _ p hp hpK
  refine ⟨frobVar_AA_eq K hp hpK (by decide), ?_⟩
  have h := frobVar_AA_eq K hp hpK (x := 1) (y := 0) (by decide)
  rw [mul_comm (at1 0 (lgF K p))]
  exact h
end Formalism.InvariantFactorPaths.G7
