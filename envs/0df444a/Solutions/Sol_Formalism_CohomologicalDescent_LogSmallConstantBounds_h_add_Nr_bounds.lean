-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.h_add_Nr_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:06.319588+00:00
-- url     : https://prove2.me/submissions/087f56eb-daeb-4f86-a169-19790d8fd1a1

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_b__eef42fd5826a
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_add_seven_le_h
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLJ_holds
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
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) :
    P.h ≤ P.h + (P.Nr : ℝ) ∧ 1 < P.h + (P.Nr : ℝ) ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      0 < Real.log (P.h + (P.Nr : ℝ)) ∧ Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 1.1 := by
  have hb := b_pos' P
  have hLJ := paramsLJ_holds P H G
  have h7 := b_add_seven_le_h H
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  have h3 := log_three_le_eleven_tenths
  refine ⟨by linarith, by linarith, hLJ.2.2.1, Real.log_pos (by linarith), ?_⟩
  have : Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 11 / 10 := by
    calc Real.log (P.h + (P.Nr : ℝ)) ≤ Real.log (3 * P.b) := Real.log_le_log (by linarith) hLJ.2.2.1
      _ = Real.log 3 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
      _ ≤ P.L + 11 / 10 := by linarith
  have d : (1.1 : ℝ) = 11 / 10 := by norm_num
  rw [d]
  exact this
end Formalism.CohomologicalDescent.LogSmallConstantBounds
