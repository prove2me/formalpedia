-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLog_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:13.556783+00:00
-- url     : https://prove2.me/submissions/a300b510-33ef-4fd4-91ee-6c47a7e7146f

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_natBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_three_mul_h_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_three_mul_h_pos_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJ_eq_div
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_lJDenom_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
private theorem log_two_le_seven_tenths : Real.log 2 ≤ 7 / 10 := by
  have h := Real.log_two_lt_d9
  have d : (0.6931471808 : ℝ) = 6931471808 / 10000000000 := by norm_num
  rw [d] at h
  linarith
private theorem log_three_le_eleven_tenths : Real.log 3 ≤ 11 / 10 := by
  have h1 : Real.log (243 / 256 : ℝ) ≤ 243 / 256 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (243 / 256 : ℝ) = 5 * Real.log 3 - 8 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (243 : ℝ) = 3 ^ 5 by norm_num,
      show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h3 := Real.log_two_lt_d9
  have d : (0.6931471808 : ℝ) = 6931471808 / 10000000000 := by norm_num
  rw [d] at h3
  linarith
private theorem log_six_le' : Real.log 6 ≤ 9 / 5 := by
  have e : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h1 := log_two_le_seven_tenths
  have h2 := log_three_le_eleven_tenths
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : Elem_a := by
  intro P H G
  have nb := natBounds H
  have hb := b_pos' P
  obtain ⟨h1, h2⟩ := log_three_mul_h_bounds H G
  obtain ⟨c1, c2⟩ := log_three_mul_h_pos_le H G
  have h6 := log_six_le'
  have hL := G.L_ge
  refine ⟨h2, by linarith, ?_⟩
  rw [lJ_eq_div, div_le_iff₀ (lJDenom_pos H G)]
  unfold indexDenominator
  have e1 : (P.m : ℝ) ≤ P.k * (P.m + P.t) := by
    nlinarith [nb.mlek, nb.k1, nb.t6, nb.m1]
  have e2 : (P.m : ℝ) * P.L ≤ P.k * (P.m + P.t) * Real.log (3 * P.h) :=
    mul_le_mul e1 h1 (by linarith) (by nlinarith [nb.k1, nb.t6, nb.m1])
  nlinarith [mul_le_mul_of_nonneg_left e2 hb.le]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
