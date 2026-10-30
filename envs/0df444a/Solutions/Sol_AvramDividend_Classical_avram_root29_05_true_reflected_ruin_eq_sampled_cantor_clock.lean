-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:07:08.173983+00:00
-- url     : https://prove2.me/submissions/823e0df6-c08d-4071-b03c-daea33b8dbd9

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- On each genuine Lévy sample path, the first strict reflected drawdown ruin
clock equals the countable normalized-record clock used by measurable rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨅ j : ℕ,
       if X.X (samples j) ω - X.X 0 ω -
           (⨆ k : ℕ,
             if samples k ≤ samples j then
               ENNReal.ofReal (X.X (samples k) ω - X.X 0 ω)
             else 0).toReal < -a then
         (samples j : ℝ≥0∞) else ⊤) := by
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hdense : Dense (Set.range samples) := by
    simpa [samples] using chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range samples := by
    refine ⟨Nat.pair 0 0, ?_⟩
    simp [samples]
  have hrec (j : ℕ) :
      (⨆ k : ℕ, if samples k ≤ samples j then
        ENNReal.ofReal (X.X (samples k) ω - X.X 0 ω) else 0).toReal =
      runningSup X (samples j) ω := by
    simpa [X.X_zero ω] using
      (avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
        X ω samples hdense hzero (samples j) ⟨j, rfl⟩)
  rw [reflectedRuin_strictClock_eq_countableSchedule X ω a]
  change (⨅ j : ℕ,
    if X.X (samples j) ω - runningSup X (samples j) ω < -a then
      (samples j : ℝ≥0∞) else ⊤) =
    (⨅ j : ℕ,
      if X.X (samples j) ω - X.X 0 ω -
          (⨆ k : ℕ, if samples k ≤ samples j then
            ENNReal.ofReal (X.X (samples k) ω - X.X 0 ω)
          else 0).toReal < -a then
        (samples j : ℝ≥0∞) else ⊤)
  apply iInf_congr
  intro j
  rw [← hrec j, X.X_zero ω]
  simp only [sub_zero]
