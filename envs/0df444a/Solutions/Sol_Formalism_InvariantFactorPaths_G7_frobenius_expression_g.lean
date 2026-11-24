-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.frobenius_expression_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:45:58.436152+00:00
-- url     : https://prove2.me/submissions/27f5edbb-9224-4470-80f0-01e190cb2255

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_identity_b

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
theorem _root_.solution : FrobExprG := by
  intro K _ p c c' hp hpK
  have hp0 : p ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := identity_b K p hp hpK
  unfold Gser
  rw [frobVar_eq_expand hp0, map_sub, map_mul, map_mul, MvPowerSeries.expand_C,
    MvPowerSeries.expand_C, ← frobVar_eq_expand hp0, ← frobVar_eq_expand hp0, h1, h2]
  ring
end Formalism.InvariantFactorPaths.G7
