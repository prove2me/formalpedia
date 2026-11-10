-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:01:53.446566+00:00
-- url     : https://prove2.me/submissions/f643d1e8-7c14-4c1f-b893-fa908b45ff54

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_measurable_mark_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_shifted_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Translate marked jump weights along the original path without changing probability spaces. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u => (u, Y u - Function.leftLim Y u))
  let ν : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hMark : Measurable (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)) := by
    simpa only [Y] using
      avram_bv_jump8_turn14_original_shifted_mark_map_measurable X ω s
  have hRect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 T ×ˢ B) = ν (Ioc s (s + T) ×ˢ B) := by
    intro B hB
    rw [show μ (Ioc 0 T ×ˢ B) =
      ({u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
        Y u - Function.leftLim Y u ≠ 0 ∧
        Y u - Function.leftLim Y u ∈ B}).encard from
      avram_bv_jump8_generic_measurable_mark_rectangle_encard Y hMark 0 T B hB]
    simpa only [μ, ν, Y, and_self_left] using
      (avram_wave5_01_actual_source_futurepath_marked_count_transport X ω s T B hB).symm
  exact avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality μ ν s T g hg hRect
