-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.thinSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:48.377504+00:00
-- url     : https://prove2.me/submissions/d0334888-677e-4f8c-ae05-c687834bef02

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_subset_primesLe
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_le_prime_cast
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_choose_two_le_sq_div_two
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_hw_le_two_mul_b__ce7bc3374f49

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : SumA := by
  intro hpc P H G ι D hA hW τ hτ Q hQ
  have hb' := H.b'_pos
  have hRHS : 0 ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b' := mul_nonneg (by positivity) hb'.le
  have hhw := hw_le_two_mul_b' H G hW hτ
  by_cases hw1 : D.hw τ ≤ 1
  · have : ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have h2 := two_le_prime_cast (hQ l hl)
      rw [(hA τ hτ l (hQ l hl)).1 (by linarith), Nat.cast_zero, zero_mul]
    rw [this]
    exact hRHS
  · push_neg at hw1
    have hlogpos : 0 < Real.log (D.hw τ) := Real.log_pos hw1
    have hC := choose_two_le_sq_div_two P.Nr
    have hC0 : (0 : ℝ) ≤ (P.Nr.choose 2 : ℝ) := Nat.cast_nonneg _
    have hsub : Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ) ⊆ pr (D.hw τ) :=
      subset_primesLe (by linarith) (fun l hl => by
        rw [Finset.mem_filter] at hl
        exact ⟨hQ l hl.1, hl.2⟩)
    have hcard : ((Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ)).card : ℝ) ≤ ((pr (D.hw τ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hpcb := hpc (D.hw τ) hw1
    have hne := hlogpos.ne'
    have hM : 0 ≤ (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ) := mul_nonneg hC0 hlogpos.le
    calc ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ)
        = ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ), (D.ex τ l : ℝ) * Real.log (l : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro l hl
          split_ifs with h
          · rfl
          · rw [(hA τ hτ l (hQ l hl)).1 (not_le.1 h), Nat.cast_zero, zero_mul]
      _ ≤ ∑ l ∈ Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ), (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ) := by
          apply Finset.sum_le_sum
          intro l hl
          rw [Finset.mem_filter] at hl
          exact (hA τ hτ l (hQ l hl.1)).2 hl.2
      _ = ((Q.filter (fun l : ℕ => (l : ℝ) ≤ D.hw τ)).card : ℝ) * ((P.Nr.choose 2 : ℝ) * Real.log (D.hw τ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((pr (D.hw τ)).card : ℝ) * ((P.Nr.choose 2 : ℝ) * Real.log (D.hw τ)) :=
          mul_le_mul_of_nonneg_right hcard hM
      _ ≤ (1.26 * D.hw τ / Real.log (D.hw τ)) * ((P.Nr.choose 2 : ℝ) * Real.log (D.hw τ)) :=
          mul_le_mul_of_nonneg_right hpcb.le hM
      _ = 1.26 * D.hw τ * (P.Nr.choose 2 : ℝ) := by
          field_simp
          try ring
      _ ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b' := by
          have k1 := mul_le_mul hhw hC hC0 (by linarith : (0 : ℝ) ≤ 2 * P.b')
          have k2 : 0 ≤ D.hw τ * (P.Nr.choose 2 : ℝ) := mul_nonneg (by linarith) hC0
          have k3 : 0 ≤ P.b' * (P.Nr : ℝ) ^ 2 := mul_nonneg hb'.le (sq_nonneg _)
          have d1 : (1.26 : ℝ) = 63 / 50 := by norm_num
          have d2 : (1.3 : ℝ) = 13 / 10 := by norm_num
          rw [d1, d2]
          nlinarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
