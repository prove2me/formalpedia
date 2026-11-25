-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.ex_mul_log_le_of_thinA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:47.634788+00:00
-- url     : https://prove2.me/submissions/b3d031a6-a012-46e3-bd08-b5b81791e6d5

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_b__eef42fd5826a
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_le_prime_cast
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_choose_two_le_sq_div_two
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_smaller_exponent_lt
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
end Formalism.CohomologicalDescent.LogSmallConstantBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hA : D.ThinA P) (hW : D.Widths P) {τ : ι} (hτ : τ ∉ D.T2) {l : ℕ} (hl : l.Prime) :
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr : ℝ) ^ 2 * P.L := by
  obtain ⟨h1, h2⟩ := hA τ hτ l hl
  have hl2 := two_le_prime_cast hl
  have hL := G.L_ge
  by_cases hlw : D.hw τ < l
  · rw [h1 hlw, Nat.cast_zero, zero_mul]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  · push_neg at hlw
    have hhw := hw_le_two_mul_b' H G hW hτ
    have hbb := smaller_exponent_lt H G
    have hb := b_pos' P
    have h2' := log_two_le_seven_tenths
    have hlog : Real.log (D.hw τ) ≤ 2 * P.L := by
      calc Real.log (D.hw τ) ≤ Real.log (2 * P.b) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + P.L := by rw [Real.log_mul (by norm_num) hb.ne', log_b']
        _ ≤ 2 * P.L := by linarith
    have hlog0 : 0 ≤ Real.log (D.hw τ) := Real.log_nonneg (by linarith)
    have hC := choose_two_le_sq_div_two P.Nr
    calc (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ) := h2 hlw
      _ ≤ ((P.Nr : ℝ) ^ 2 / 2) * (2 * P.L) := mul_le_mul hC hlog hlog0 (by positivity)
      _ = (P.Nr : ℝ) ^ 2 * P.L := by ring
end Formalism.CohomologicalDescent.LogSmallConstantBounds
