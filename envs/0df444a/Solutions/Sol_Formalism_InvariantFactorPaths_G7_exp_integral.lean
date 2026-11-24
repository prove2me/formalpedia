-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:41.468803+00:00
-- url     : https://prove2.me/submissions/c43ae057-2ea0-4fd3-ad78-4930af99aeae

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_exponential_weight_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
theorem _root_.solution : ExpIntegral := by
  intro K ι _ _ _ p hp hnp f hf0 hf n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlt : ‖(p : K)‖ < 1 := by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  have hd : ∀ m : ι →₀ ℕ, Formalism.DworkPowerSeriesWeights.dot m (fun _ => (0 : ℝ)) = 0 := by
    intro m; simp [Formalism.DworkPowerSeriesWeights.dot]
  have h := Formalism.DworkPowerSeriesWeights.exponential_weight_le.{0, 0} K p hp hlt ι (fun _ => 0) n f hf0 (by
    intro m _
    rw [Formalism.DworkPowerSeriesWeights.monoWtGe_iff, hd, sub_zero, hnp, Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
    exact hf m) n le_rfl
  rw [Formalism.DworkPowerSeriesWeights.monoWtGe_iff, hd] at h
  simpa using h
end Formalism.InvariantFactorPaths.G7
