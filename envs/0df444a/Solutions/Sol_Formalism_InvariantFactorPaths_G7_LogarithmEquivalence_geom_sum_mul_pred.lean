-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:32.674895+00:00
-- url     : https://prove2.me/submissions/1a4016dd-2241-444e-9a47-ea88f6485c0e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence

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
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution {q : ℕ} (hq : 4 ≤ q) (j : ℕ) :
    ∃ g, q ^ j = (q - 1) * g + 1 ∧ j ≤ g ∧ (2 ≤ j → j + 1 ≤ g) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction j with
  | zero => exact ⟨0, by simp, le_refl _, fun h => by omega⟩
  | succ j ih =>
    obtain ⟨g, h1, h2, _⟩ := ih
    refine ⟨(r + 1) * g + 1, by rw [pow_succ, h1]; ring, by nlinarith, fun h => ?_⟩
    have hg : 1 ≤ g := by omega
    nlinarith
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
