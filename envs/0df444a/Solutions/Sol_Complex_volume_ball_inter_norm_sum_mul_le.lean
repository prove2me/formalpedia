-- Prove2me | solution 1 for Complex.volume_ball_inter_norm_sum_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/31d6ee53-4a84-5d5a-be73-cabf0cf0d78d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_volume_ball_inter_norm_sum_mul_le

open MeasureTheory Metric

theorem solution {n : ℕ} (w : Fin n → ℂ) (hw : w ≠ 0) (ε : ℝ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε}
      ≤ ENNReal.ofReal ((ε / ‖w‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1) := by

  rcases lt_or_ge ε 0 with hε | hε
  · have h0 : {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro _
      exact hε.trans_le (norm_nonneg _)
    rw [h0, measure_empty]
    exact bot_le

  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd (Subsingleton.elim w 0) hw
    | succ m => exact ⟨m, rfl⟩

  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => ‖w j‖
  have hnorm : ‖w‖ = ‖w j₀‖ :=
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj₀) (norm_le_pi_norm w j₀)
  have hw₀ : w j₀ ≠ 0 := by
    intro h
    apply hw
    have : ‖w‖ = 0 := by rw [hnorm, h, norm_zero]
    exact norm_eq_zero.1 this
  have hw₀' : 0 < ‖w j₀‖ := norm_pos_iff.2 hw₀

  have hemp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) j₀) volume volume :=
    volume_preserving_piFinSuccAbove _ j₀
  have he : ∀ b : Fin (m + 1) → ℂ,
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) j₀ b = (b j₀, fun j => b (j₀.succAbove j)) :=
    fun _ => rfl

  set g : (Fin m → ℂ) → ℂ := fun b' => ∑ j, b' j * w (j₀.succAbove j) with hg
  have hgc : Continuous g := by
    rw [hg]
    fun_prop

  set T : Set (ℂ × (Fin m → ℂ)) := {p | p.2 ∈ Metric.ball 0 1 ∧ ‖p.1 * w j₀ + g p.2‖ ≤ ε} with hT
  have hTmeas : MeasurableSet T := by
    change MeasurableSet ((Prod.snd ⁻¹' Metric.ball (0 : Fin m → ℂ) 1) ∩ {p : ℂ × (Fin m → ℂ) | ‖p.1 * w j₀ + g p.2‖ ≤ ε})
    exact (measurableSet_ball.preimage measurable_snd).inter
      (isClosed_le ((continuous_fst.mul continuous_const).add (hgc.comp continuous_snd)).norm
        continuous_const).measurableSet
  have hsub : {b : Fin (m + 1) → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε}
      ⊆ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) j₀ ⁻¹' T := by
    rintro b ⟨hb1, hb2⟩
    rw [Set.mem_preimage, he]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff] at hb1 ⊢
      refine lt_of_le_of_lt ?_ hb1
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm b (j₀.succAbove j)
    · rw [Fin.sum_univ_succAbove _ j₀] at hb2
      exact hb2

  have hfib : ∀ b' : Fin m → ℂ, volume ((fun x : ℂ => (x, b')) ⁻¹' T)
      ≤ (Metric.ball (0 : Fin m → ℂ) 1).indicator
          (fun _ => ENNReal.ofReal (ε / ‖w j₀‖) ^ 2 * (NNReal.pi : ENNReal)) b' := by
    intro b'
    by_cases hb' : b' ∈ Metric.ball (0 : Fin m → ℂ) 1
    · rw [Set.indicator_of_mem hb', ← Complex.volume_closedBall (-(g b' / w j₀)) (ε / ‖w j₀‖)]
      refine measure_mono fun x hx => ?_
      simp only [Set.mem_preimage, hT, Set.mem_setOf_eq] at hx
      obtain ⟨-, hx⟩ := hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hxe : x - -(g b' / w j₀) = (x * w j₀ + g b') / w j₀ := by
        rw [sub_neg_eq_add, add_div' _ _ _ hw₀]
      rw [hxe, norm_div, div_le_div_iff_of_pos_right hw₀']
      exact hx
    · rw [Set.indicator_of_notMem hb']
      have h0 : (fun x : ℂ => (x, b')) ⁻¹' T = ∅ := by
        ext x
        simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hb' h.1
      rw [h0, measure_empty]
  calc volume {b : Fin (m + 1) → ℂ | b ∈ Metric.ball 0 1 ∧ ‖∑ j, b j * w j‖ ≤ ε}
      ≤ volume (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) j₀ ⁻¹' T) := measure_mono hsub
    _ = volume T := hemp.measure_preimage_equiv T
    _ = ∫⁻ b', volume ((fun x : ℂ => (x, b')) ⁻¹' T) := by
        rw [Measure.volume_eq_prod ℂ (Fin m → ℂ)]
        exact Measure.prod_apply_symm hTmeas
    _ ≤ ∫⁻ b', (Metric.ball (0 : Fin m → ℂ) 1).indicator
          (fun _ => ENNReal.ofReal (ε / ‖w j₀‖) ^ 2 * (NNReal.pi : ENNReal)) b' := lintegral_mono hfib
    _ = ENNReal.ofReal (ε / ‖w j₀‖) ^ 2 * (NNReal.pi : ENNReal) * volume (Metric.ball (0 : Fin m → ℂ) 1) :=
        lintegral_indicator_const measurableSet_ball _
    _ = ENNReal.ofReal ((ε / ‖w‖) ^ 2) * volume (Metric.ball (0 : Fin (m + 1) → ℂ) 1) := by
        rw [volume_pi_ball _ one_pos, volume_pi_ball _ one_pos]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply, Complex.volume_ball,
          ENNReal.ofReal_one, one_pow, one_mul]
        rw [hnorm, ENNReal.ofReal_pow (div_nonneg hε (norm_nonneg _)), pow_succ]
        ring

end S_Complex_volume_ball_inter_norm_sum_mul_le
end P2MW
export P2MW.S_Complex_volume_ball_inter_norm_sum_mul_le (solution)
