-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.class_exponential
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.091607+00:00
-- url     : https://prove2.me/submissions/5d55432f-d795-426b-a2ae-e0ed7238645c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_mvExp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_pi_factorial

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
theorem _root_.solution : ClassExp := by
  intro K ι _ _ _ p ϖ hp hnp hϖ hh hh0
  classical
  refine ⟨fun i => MvPowerSeries.C ((-1) ^ i * (ϖ ^ ((p + 1) * i) / (i.factorial : K))), ?_, ?_⟩
  · intro i n
    rw [MvPowerSeries.coeff_C]
    split_ifs
    · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact pi_factorial K p ϖ hp hnp hϖ i
    · simp
  · intro n
    have h0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)) = 0 := by
      simp [hh0]
    rw [coeff_mvExp h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)) ^ k =
        MvPowerSeries.C ((-(ϖ ^ (p + 1) / (p : K))) ^ k) * hh ^ k := by
      rw [← neg_mul, ← map_neg, mul_pow, ← map_pow]
    rw [e, MvPowerSeries.coeff_C_mul, mul_comm (hh ^ k), MvPowerSeries.coeff_C_mul, neg_pow, div_pow,
      ← pow_mul]
    ring
end Formalism.InvariantFactorPaths.G7
