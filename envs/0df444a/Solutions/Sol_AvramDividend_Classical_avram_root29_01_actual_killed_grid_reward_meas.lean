-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:38:42.455705+00:00
-- url     : https://prove2.me/submissions/711194e9-c1e8-4815-8fab-61a65f83c75c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_grid_hitting_index_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_random_grid_history_meas
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine lower-history-killed discounted q-scale reward at
the actual sampled first-outside index is globally measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      ({η : Ω | ∀ t : ℝ≥0,
        t ≤ clock (K η) → 0 ≤ x + X.X t η}).indicator
          (fun η => Real.exp (-(q * (clock (K η) : ℝ))) *
            W (x + X.X (clock (K η)) η)) ω) := by
  have hKm : Measurable K :=
    avram_root29_01_actual_grid_hitting_index_meas
      X clock H hH lower upper m K hK
  have hB : MeasurableSet {η : Ω | ∀ t : ℝ≥0,
      t ≤ clock (K η) → 0 ≤ x + X.X t η} :=
    avram_root29_01_actual_random_grid_history_meas
      X x clock K hKm
  obtain ⟨hStopped, hTime⟩ :=
    chat03_grid_stopped_reserve_time_measurable
      X clock H hH lower upper m K hK
  have hScale : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hDiscount : Measurable (fun η : Ω =>
      Real.exp (-(q * (clock (K η) : ℝ)))) := by
    exact (measurable_const.mul hTime).neg.exp
  have hValue : Measurable (fun η : Ω =>
      W (x + X.X (clock (K η)) η)) := by
    exact hScale.comp (measurable_const.add hStopped)
  exact (hDiscount.mul hValue).indicator hB
