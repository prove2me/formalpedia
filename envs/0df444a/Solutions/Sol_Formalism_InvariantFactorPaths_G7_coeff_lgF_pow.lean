-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_lgF_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:58.02505+00:00
-- url     : https://prove2.me/submissions/0114df39-d777-48f5-8669-98865d3b59f5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_range_ite_unique

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
theorem _root_.solution (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ j) (lgF K p) = ((p : K) ^ j)⁻¹ := by
  unfold lgF
  rw [PowerSeries.coeff_mk]
  exact sum_range_ite_unique _ (fun i => (p ^ 2) ^ j = (p ^ 2) ^ i) (fun i => ((p : K) ^ i)⁻¹) j
    (lt_powq hp j) rfl (fun i h => powq_inj hp h.symm)
end Formalism.InvariantFactorPaths.G7
