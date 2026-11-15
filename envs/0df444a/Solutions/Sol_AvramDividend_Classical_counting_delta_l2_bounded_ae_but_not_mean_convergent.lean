-- Prove2me | solution 1 for AvramDividend.Classical.counting_delta_l2_bounded_ae_but_not_mean_convergent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:51:20.799193+00:00
-- url     : https://prove2.me/submissions/f8092ddf-c927-4183-9637-a4741d0fa554

import Mathlib
import Theorems.Thm_AvramDividend_Classical_counting_delta_indicator_mean_and_pointwise_zero
import Theorems.Thm_AvramDividend_Classical_counting_delta_l1_l2_norm_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section
theorem solution :
    ∃ Y : ℕ → ℕ → ℝ,
      (∀ n, eLpNorm (Y n) 2 (Measure.count : Measure ℕ) = 1) ∧
      (∀ n, eLpNorm (Y n) 1 (Measure.count : Measure ℕ) = 1) ∧
      (∀ᵐ ω ∂(Measure.count : Measure ℕ),
        Tendsto (fun n => Y n ω) atTop (nhds (0 : ℝ))) ∧
      ¬ Tendsto (fun n => ∫ ω, Y n ω ∂(Measure.count : Measure ℕ))
        atTop (nhds (0 : ℝ)) := by
  let Y : ℕ → ℕ → ℝ := fun n => ({n} : Set ℕ).indicator (fun _ => 1)
  have h := AvramDividend.Classical.counting_delta_indicator_mean_and_pointwise_zero
  have hn := AvramDividend.Classical.counting_delta_l1_l2_norm_one
  refine ⟨Y, (fun n => (hn n).2), (fun n => (hn n).1), ?_, ?_⟩
  · exact Filter.Eventually.of_forall h.2
  · intro hm
    have hMean :
        (fun n : ℕ => ∫ ω, Y n ω ∂(Measure.count : Measure ℕ)) =
          (fun _ : ℕ => (1 : ℝ)) := funext h.1
    rw [hMean] at hm
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hm)
