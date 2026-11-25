-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.largePrimeSumElementary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:13.396454+00:00
-- url     : https://prove2.me/submissions/eb1daafe-f53c-4a37-91d7-567de4ecda38

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsBasic_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_add_seven_le_h
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_prime_of_mem_primesLe
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_le_prime_cast
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_prime_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_h_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_eight_lt_lJ
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_min_cW_le_split
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_h_add_Nr_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_subset_primesLe_h_add_Nr
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_div_prime_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_residueIndicator_mul_log_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_gateTerm_mul_log_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_one_add_log_div_le
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_q_j_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_chebyshevThetaElementary_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_mertensLogElementary_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_small_terms_le_of_log_four
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
private theorem log_h_pos_and_le {P : Par} (H : P.Hyp) (G : P.Large) :
    0 < Real.log P.h ∧ Real.log P.h ≤ P.L + 7 / 10 := by
  obtain ⟨h1, h2⟩ := log_h_bounds H G
  have d : (0.7 : ℝ) = 7 / 10 := by norm_num
  rw [d] at h2
  exact ⟨h1, h2⟩
private theorem h_add_Nr_bounds_and_log_bounds {P : Par} (H : P.Hyp) (G : P.Large) :
    1 < P.h + (P.Nr : ℝ) ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      0 < Real.log (P.h + (P.Nr : ℝ)) ∧ Real.log (P.h + (P.Nr : ℝ)) ≤ P.L + 11 / 10 := by
  obtain ⟨_, h1, h2, h3, h4⟩ := h_add_Nr_bounds H G
  have d : (1.1 : ℝ) = 11 / 10 := by norm_num
  rw [d] at h4
  exact ⟨h1, h2, h3, h4⟩
private theorem mul_mul_le_mul_mul {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : a * b * c ≤ a' * b' * c' :=
  mul_le_mul (mul_le_mul ha hb hb0 (ha0.trans ha)) hc hc0
    (mul_nonneg (ha0.trans ha) (hb0.trans hb))
private theorem log_four_le' : Real.log 4 ≤ 139 / 100 := by
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have := Real.log_two_lt_d9
  norm_num at this
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
theorem _root_.solution : SumDE := by
  intro P H G ι D hA hC hT hNW τ hτ Q hQ
  have hb := b_pos' P
  have hL := G.L_ge
  have hsplit := sum_min_cW_le_split H G hA hC hNW hτ hQ
  set R := Q.filter (fun l : ℕ => (l : ℝ) ≤ P.h) with hRdef
  have hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h := by
    intro l hl
    rw [hRdef, Finset.mem_filter] at hl
    exact ⟨(hQ l hl.1).1, (hQ l hl.1).2.1, hl.2⟩
  have hJ8 := eight_lt_lJ H G
  obtain ⟨c1, c2⟩ := log_h_pos_and_le H G
  have hh := (paramsBasic_holds P H G).2.2
  have h7 := b_add_seven_le_h H
  obtain ⟨hq, hqj, hq0, hj0⟩ := q_j_bounds hT hτ
  obtain ⟨n1, n2, n3, n4⟩ := h_add_Nr_bounds_and_log_bounds H G
  have z1 : 0 ≤ ∑ l ∈ R, Real.log (l : ℝ) / ((l : ℝ) - 1) := Finset.sum_nonneg (fun l hl => by
    have hl2 := two_le_prime_cast (hR l hl).1
    exact div_nonneg (log_prime_nonneg (hR l hl).1) (by linarith))
  have z2 : 0 ≤ ∑ l ∈ R, Real.log (l : ℝ) :=
    Finset.sum_nonneg (fun l hl => log_prime_nonneg (hR l hl).1)
  have z3 : 0 ≤ ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) :=
    Finset.sum_nonneg (fun l hl => log_div_prime_nonneg (hR l hl).1)
  have z6 : 0 ≤ ∑ l ∈ R, (1 + max 0 (Real.log (P.h / (l : ℝ)))) * (Real.log (l : ℝ) / (l : ℝ)) :=
    Finset.sum_nonneg (fun l hl => mul_nonneg
      (by have := le_max_left (0 : ℝ) (Real.log (P.h / (l : ℝ))); linarith)
      (log_div_prime_nonneg (hR l hl).1))
  have hm0 : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hm2b : (0 : ℝ) ≤ P.m * (2 * P.b) := mul_nonneg hm0 (by linarith)
  have hmb : 0 ≤ (P.m : ℝ) * P.b := mul_nonneg hm0 hb.le
  have hmbL : 0 ≤ (P.m : ℝ) * P.b * P.L := mul_nonneg hmb (by linarith)
  have u1 : (D.q τ : ℝ) * P.h ≤ P.m * (2 * P.b) := mul_le_mul hq hh (by linarith) hm0
  have pred : ∑ l ∈ R, Real.log (l : ℝ) / ((l : ℝ) - 1) ≤
      9 / 8 * ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hp, hlt, _⟩ := hR l hl
    have h8' : 8 < l := by exact_mod_cast (show (8 : ℝ) < l by linarith)
    have h9 : (9 : ℝ) ≤ l := by exact_mod_cast (show 9 ≤ l by omega)
    have hl0 : (l : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have e : Real.log (l : ℝ) / (l : ℝ) * ((l : ℝ) / ((l : ℝ) - 1)) = Real.log (l : ℝ) / ((l : ℝ) - 1) := by
      rw [div_mul_div_comm, mul_comm (Real.log (l : ℝ)) (l : ℝ), mul_div_mul_left _ _ hl0]
    have hq98 : (l : ℝ) / ((l : ℝ) - 1) ≤ 9 / 8 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    rw [← e]
    have := mul_le_mul_of_nonneg_left hq98 (log_div_prime_nonneg hp)
    linarith
  have hNr0 : (0 : ℝ) ≤ P.Nr := Nat.cast_nonneg _
  have hsub := subset_primesLe_h_add_Nr H G hR
  have s2 : ∑ l ∈ R, Real.log (l : ℝ) ≤ Real.log 4 * (P.h + (P.Nr : ℝ)) := by
    have a := chebyshevThetaElementary_holds (P.h + (P.Nr : ℝ)) (by linarith)
    have b : ∑ l ∈ R, Real.log (l : ℝ) ≤ ∑ p ∈ pr (P.h + (P.Nr : ℝ)), Real.log (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => log_prime_nonneg (prime_of_mem_primesLe hp))
    linarith
  have s3 : ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) ≤ Real.log (P.h + (P.Nr : ℝ)) + Real.log 4 := by
    have a := mertensLogElementary_holds (P.h + (P.Nr : ℝ)) (by linarith)
    have b : ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) ≤ ∑ p ∈ pr (P.h + (P.Nr : ℝ)), Real.log (p : ℝ) / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => log_div_prime_nonneg (prime_of_mem_primesLe hp))
    linarith
  have s4 := sum_residueIndicator_mul_log_le H G hT hτ hR
  have s5 := sum_gateTerm_mul_log_le H G hT hτ hR
  have st := small_terms_le_of_log_four H G _ _ s3 s4
  have h4 := log_four_le'
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA3 : ∑ l ∈ R, Real.log (l : ℝ) / (l : ℝ) ≤ P.L + 249 / 100 := by linarith
  have hA2 : ∑ l ∈ R, Real.log (l : ℝ) ≤ 139 / 100 * (3 * P.b) := by
    have := mul_le_mul h4 n2 (by linarith) (by norm_num)
    linarith
  have hBl : ∀ l ∈ R, Real.log (P.h / (l : ℝ)) ≤ P.L + 7 / 10 := by
    intro l hl
    have hl2 := two_le_prime_cast (hR l hl).1
    have : Real.log (P.h / (l : ℝ)) ≤ Real.log P.h :=
      Real.log_le_log (div_pos (by linarith) (by linarith)) (div_le_self (by linarith) (by linarith))
    linarith
  have s6 := sum_one_add_log_div_le hR (P.L + 7 / 10) (by linarith) hBl
  have t1 := mul_mul_le_mul_mul hqj n2 (pred.trans (mul_le_mul_of_nonneg_left hA3 (by norm_num)))
    (by linarith) (by linarith) z1
  have t2 : 6 * ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ∑ l ∈ R, Real.log (l : ℝ)
      ≤ 6 * (2 * (P.m : ℝ)) * (139 / 100 * (3 * P.b)) :=
    mul_le_mul (by linarith) hA2 z2 (by linarith)
  have u2 : (1 + Real.log P.h) * Real.log P.h ≤ (P.L + 17 / 10) * (P.L + 7 / 10) :=
    mul_le_mul (by linarith) c2 c1.le (by linarith)
  have u3 := mul_le_mul u1 u2 (mul_nonneg (by linarith) c1.le) hm2b
  have u4 := mul_le_mul_of_nonneg_left hA3 (by linarith : (0 : ℝ) ≤ 1 + (P.L + 7 / 10))
  have u5 := mul_le_mul u1 (s6.trans u4) z6 hm2b
  have d25 : (2.5 : ℝ) = 5 / 2 := by norm_num
  rw [d25]
  constructor
  · linarith
  · have hq14 : (0 : ℝ) ≤ 14 * (P.L - 4) ^ 2 + 83 * (P.L - 4) + 9 := by nlinarith
    linarith [mul_nonneg hmb hq14]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
