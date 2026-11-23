-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.lt_ppowq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:23.690425+00:00
-- url     : https://prove2.me/submissions/790d3d4a-6f44-4de9-b2bf-f02b1bdea6cc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq

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
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : j < p * (p ^ 2) ^ j + 1 := by
  have h1 := lt_powq hp j
  nlinarith [Nat.zero_le ((p ^ 2) ^ j)]
end Formalism.InvariantFactorPaths.G7
