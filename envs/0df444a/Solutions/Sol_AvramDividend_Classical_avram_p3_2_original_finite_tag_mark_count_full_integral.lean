-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_finite_tag_mark_count_full_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:34:21.728204+00:00
-- url     : https://prove2.me/submissions/f1db661f-ecf6-450f-a9d3-2a11ed2b6a41

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Finite tagged original Lévy jumps are counted exactly once by the
nonlinear original marked counting integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : Finset ℝ≥0)
    (hT : ∀ t ∈ T, 0 < t ∧
      X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p,
      (if p.1 ∈ (T : Set ℝ≥0) then F p else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ t ∈ T, F (t,
        X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t) := by
  have hPair : Measurable (fun u : ℝ≥0 => (u, ω)) :=
    measurable_id.prodMk measurable_const
  have hSection : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hPair
  have hMark : Measurable (fun u : ℝ≥0 => (u,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) :=
    measurable_id.prodMk hSection
  have hSet :=
    avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
      X ω hMark
  have hMeas : Measurable
      (fun p : ℝ≥0 × ℝ => if p.1 ∈ (T : Set ℝ≥0) then F p else 0) :=
    Measurable.ite (T.measurableSet.preimage measurable_fst) hF measurable_const
  rw [lintegral_map hMeas hMark]
  rw [← lintegral_indicator hSet]
  rw [lintegral_count]
  rw [tsum_eq_sum (s := T) (by
    intro t ht
    simp [Set.indicator, ht])]
  apply Finset.sum_congr rfl
  intro t ht
  simp [Set.indicator, ht, (hT t ht).1, (hT t ht).2]
