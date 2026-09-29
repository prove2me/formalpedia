-- Prove2me | solution 1 for Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6fc630fa-c227-5a3b-a218-d4eca5492175

import Mathlib
import Theorems.Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le
import Theorems.Thm_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume

open MeasureTheory Metric
open scoped ENNReal NNReal

theorem solution {n : ℕ} (c : ℂ → Fin n → ℂ)
    (S : Set ℂ) {η L : ℝ} (hη : 0 < η) (hηc : ∀ z ∈ S, η ≤ ‖c z‖)
    (hLip : ∀ z ∈ S, ∃ δ > 0, ∀ y ∈ Metric.closedBall z δ, ‖c y - c z‖ ≤ L * ‖y - z‖) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ S, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * L / η) ^ 2 / Real.pi) * volume (Metric.ball (0 : Fin n → ℂ) 1) * volume S := by

  have hset0 : {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ S, ∑ j, b j * c z j = 0}
      = {b : Fin n → ℂ | ∃ z ∈ S, b ∈ Metric.ball 0 1 ∧ ∑ j, b j * c z j = 0} := by
    ext b; simp only [Set.mem_setOf_eq]; aesop
  rw [hset0]
  refine MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall volume volume
    (fun (b : Fin n → ℂ) (y : ℂ) => b ∈ Metric.ball 0 1 ∧ ∑ j, b j * c y j = 0) S _ ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  intro x hx
  obtain ⟨δ, hδ, hδlip⟩ := hLip x hx
  refine ⟨δ, hδ, fun ρ hρ => ?_⟩
  have hcx' : η ≤ ‖c x‖ := hηc x hx

  have hL : 0 ≤ L := by
    refine not_lt.1 fun hL => ?_
    have hy : x + δ ∈ Metric.closedBall x δ := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    have h1 := hδlip (x + δ) hy
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at h1
    exact absurd (h1.trans_lt (mul_neg_of_neg_of_pos hL hδ)) (not_lt.2 (norm_nonneg _))
  have hcx : c x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcx'
    exact absurd hcx' (not_le.2 hη)

  have hset : {b : Fin n → ℂ | ∃ y ∈ Metric.closedBall x ρ, b ∈ Metric.ball 0 1 ∧ ∑ j, b j * c y j = 0}
      = {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ y ∈ Metric.closedBall x ρ, ∑ j, b j * c y j = 0} := by
    ext b; simp only [Set.mem_setOf_eq]; aesop
  rw [hset]
  refine (Complex.volume_ball_inter_exists_sum_mul_eq_zero_le c x (Metric.closedBall x ρ) hcx
    (δ := L * ρ) fun y hy => ?_).trans ?_
  · exact (hδlip y (Metric.closedBall_subset_closedBall hρ.2.le hy)).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hy) hL)
  · rw [Complex.volume_closedBall]
    have hpi : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    have hρ0 : 0 ≤ ρ := hρ.1.le
    have hreal : (n * (L * ρ) / ‖c x‖) ^ 2 ≤ (n * L / η) ^ 2 / Real.pi * (ρ ^ 2 * Real.pi) := by
      rw [div_pow]
      calc (n * (L * ρ)) ^ 2 / ‖c x‖ ^ 2 ≤ (n * (L * ρ)) ^ 2 / η ^ 2 :=
            div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hη 2) (pow_le_pow_left₀ hη.le hcx' 2)
        _ = (n * L / η) ^ 2 / Real.pi * (ρ ^ 2 * Real.pi) := by
            rw [mul_comm (ρ ^ 2) Real.pi, ← mul_assoc _ Real.pi (ρ ^ 2), div_mul_cancel₀ _ Real.pi_ne_zero,
              ← mul_pow, ← div_pow]
            ring
    calc ENNReal.ofReal ((n * (L * ρ) / ‖c x‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1)
        ≤ ENNReal.ofReal ((n * L / η) ^ 2 / Real.pi * (ρ ^ 2 * Real.pi))
            * volume (Metric.ball (0 : Fin n → ℂ) 1) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) Real.pi_pos.le), ENNReal.ofReal_mul (sq_nonneg _),
            ENNReal.ofReal_pow hρ0, hpi]
          ring

end S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume
end P2MW
export P2MW.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume (solution)
