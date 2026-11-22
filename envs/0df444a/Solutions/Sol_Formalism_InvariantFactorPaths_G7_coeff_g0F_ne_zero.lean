-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_g0F_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:32.151845+00:00
-- url     : https://prove2.me/submissions/a1ef280e-2ce0-47dd-88af-dd6984914d18

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
theorem _root_.solution {K : Type} [Field K] {p n : ℕ}
    (h : PowerSeries.coeff n (g0F K p) ≠ 0) : ∃ j, n = p * (p ^ 2) ^ j := by
  unfold g0F at h
  rw [PowerSeries.coeff_mk] at h
  by_contra hc
  push_neg at hc
  apply h
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (hc i)]
end Formalism.InvariantFactorPaths.G7
