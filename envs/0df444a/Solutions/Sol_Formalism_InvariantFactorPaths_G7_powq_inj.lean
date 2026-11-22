-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.powq_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:34.348558+00:00
-- url     : https://prove2.me/submissions/3ec88acf-257e-4803-bccc-82c0bb0b2830

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {i j : ℕ} (h : (p ^ 2) ^ i = (p ^ 2) ^ j) : i = j := by
  have h2 : 2 ≤ p ^ 2 := by nlinarith
  exact Nat.pow_right_injective h2 h
end Formalism.InvariantFactorPaths.G7
