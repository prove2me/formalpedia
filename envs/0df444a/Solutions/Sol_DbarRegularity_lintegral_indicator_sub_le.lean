-- Prove2me | solution 1 for DbarRegularity.lintegral_indicator_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:37:47.224001+00:00
-- url     : https://prove2.me/submissions/d5cc30d6-24c2-46ab-9b65-fa8ef3b8083f

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- Truncating a kernel with `|K(x)| ≤ B |x|^{-d}` to `{|x| ≥ r}` changes its Hörmander integral
`∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx` by at most `C B`, with `C` depending only on `d`. -/
theorem lintegral_indicator_sub_le {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ),
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) → ∀ r : ℝ, 0 < r → ∀ y : EuclideanSpace ℝ (Fin d),
        ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖},
            ‖{x | r ≤ ‖x‖}.indicator K (x - y) - {x | r ≤ ‖x‖}.indicator K x‖ₑ ≤
          (∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ) + ENNReal.ofReal (C * B) := by
  set V := EuclideanSpace ℝ (Fin d)
  have hfin : Module.finrank ℝ V = d := finrank_euclideanSpace_fin
  refine ⟨3 ^ d * volume.real (ball (0 : V) 1), mul_nonneg (by positivity) ENNReal.toReal_nonneg, ?_⟩
  intro K B hB r hr y
  set S : Set V := {x | 2 * ‖y‖ ≤ ‖x‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  set c : ℝ≥0∞ := ENNReal.ofReal (B * (3 / (2 * r)) ^ d)
  -- the norm bound on the transition annulus
  have hKx : ∀ x : V, r * 2 / 3 ≤ ‖x‖ → ‖K x‖ₑ ≤ c := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hx; linarith
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have h1 := hB x hx0
    have hB0 : 0 ≤ B := by
      have := (norm_nonneg _).trans h1
      exact (div_nonneg_iff.1 this).elim (fun h => h.1)
        (fun h => absurd h.2 (not_le.2 (by positivity)))
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal (h1.trans ?_)
    rw [div_eq_mul_inv, ← inv_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hB0
    rw [inv_le_comm₀ hpos (by positivity)]
    calc (3 / (2 * r))⁻¹ = r * 2 / 3 := by field_simp
      _ ≤ ‖x‖ := hx
  have hpt : ∀ x ∈ S, ‖{x | r ≤ ‖x‖}.indicator K (x - y) - {x | r ≤ ‖x‖}.indicator K x‖ₑ ≤
      ‖K (x - y) - K x‖ₑ + (ball (0 : V) (2 * r)).indicator (fun _ => c) x := by
    intro x hx
    have hx' : 2 * ‖y‖ ≤ ‖x‖ := hx
    have hxy1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    have hxy2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le _ _
    by_cases ha : r ≤ ‖x - y‖ <;> by_cases hb : r ≤ ‖x‖
    · rw [indicator_of_mem (show x - y ∈ {x : V | r ≤ ‖x‖} from ha),
        indicator_of_mem (show x ∈ {x : V | r ≤ ‖x‖} from hb)]
      exact le_self_add
    · rw [indicator_of_mem (show x - y ∈ {x : V | r ≤ ‖x‖} from ha),
        indicator_of_notMem (show x ∉ {x : V | r ≤ ‖x‖} from hb), sub_zero]
      have hxb : x ∈ ball (0 : V) (2 * r) := by
        rw [mem_ball_zero_iff]; push_neg at hb; linarith
      rw [indicator_of_mem hxb]
      calc ‖K (x - y)‖ₑ = ‖(K (x - y) - K x) + K x‖ₑ := by rw [sub_add_cancel]
        _ ≤ ‖K (x - y) - K x‖ₑ + ‖K x‖ₑ := enorm_add_le _ _
        _ ≤ _ := add_le_add le_rfl (hKx x (by linarith))
    · rw [indicator_of_notMem (show x - y ∉ {x : V | r ≤ ‖x‖} from ha),
        indicator_of_mem (show x ∈ {x : V | r ≤ ‖x‖} from hb), zero_sub, enorm_neg]
      have hxb : x ∈ ball (0 : V) (2 * r) := by
        rw [mem_ball_zero_iff]; push_neg at ha; linarith
      rw [indicator_of_mem hxb]
      exact (hKx x (by linarith)).trans le_add_self
    · rw [indicator_of_notMem (show x - y ∉ {x : V | r ≤ ‖x‖} from ha),
        indicator_of_notMem (show x ∉ {x : V | r ≤ ‖x‖} from hb), sub_zero, enorm_zero]
      exact bot_le
  calc _ ≤ ∫⁻ x in S, (‖K (x - y) - K x‖ₑ + (ball (0 : V) (2 * r)).indicator (fun _ => c) x) :=
        setLIntegral_mono' hS hpt
    _ = (∫⁻ x in S, ‖K (x - y) - K x‖ₑ) + ∫⁻ x in S, (ball (0 : V) (2 * r)).indicator (fun _ => c) x :=
        lintegral_add_right _ (measurable_const.indicator measurableSet_ball)
    _ ≤ (∫⁻ x in S, ‖K (x - y) - K x‖ₑ) + ∫⁻ x, (ball (0 : V) (2 * r)).indicator (fun _ => c) x :=
        add_le_add le_rfl (setLIntegral_le_lintegral _ _)
    _ = (∫⁻ x in S, ‖K (x - y) - K x‖ₑ) + c * volume (ball (0 : V) (2 * r)) := by
        rw [lintegral_indicator_const measurableSet_ball]
    _ ≤ _ := by
        refine add_le_add le_rfl (le_of_eq ?_)
        rw [Measure.addHaar_ball_of_pos _ _ (by positivity : (0 : ℝ) < 2 * r), hfin]
        by_cases hB0 : 0 ≤ B
        · rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          have hV : volume (ball (0 : V) 1) = ENNReal.ofReal (volume.real (ball (0 : V) 1)) := by
            rw [Measure.real, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
          rw [hV, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow, mul_pow]
          field_simp
        · push_neg at hB0
          have h1 : c = 0 := by
            rw [ENNReal.ofReal_eq_zero]
            exact mul_nonpos_of_nonpos_of_nonneg hB0.le (by positivity)
          rw [h1, zero_mul]; symm; rw [ENNReal.ofReal_eq_zero]
          exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) ENNReal.toReal_nonneg) hB0.le

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ),
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) → ∀ r : ℝ, 0 < r → ∀ y : EuclideanSpace ℝ (Fin d),
        ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖},
            ‖{x | r ≤ ‖x‖}.indicator K (x - y) - {x | r ≤ ‖x‖}.indicator K x‖ₑ ≤
          (∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ) + ENNReal.ofReal (C * B) :=
  DbarRegularity.lintegral_indicator_sub_le hd
