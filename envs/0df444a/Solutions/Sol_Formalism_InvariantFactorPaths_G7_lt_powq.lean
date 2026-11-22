-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.lt_powq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:36.723845+00:00
-- url     : https://prove2.me/submissions/6e7648ec-c024-4f23-9fff-5e1c3e4edda4

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
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
private lemma lt_pow_self_of_two_le {b : ℕ} (hb : 2 ≤ b) (j : ℕ) : j < b ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : j < (p ^ 2) ^ j + 1 := by
  have := lt_pow_self_of_two_le (b := p ^ 2) (by nlinarith) j
  omega
end Formalism.InvariantFactorPaths.G7
