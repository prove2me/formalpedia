-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.alG_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.24857+00:00
-- url     : https://prove2.me/submissions/b793b5ca-ee6a-45e4-a1b4-6464ae30747b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel

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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
namespace Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
theorem _root_.solution {ν : ℕ} (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (s : ZMod (2 * ν)) : alG TT colN hts s ≤ ∑ c, hts s c := by
  unfold alG
  split_ifs
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_le_sum fun c _ => ?_
    split_ifs with h
    · exact h.ge
    · exact Nat.zero_le _
  · exact Nat.zero_le _
end Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
