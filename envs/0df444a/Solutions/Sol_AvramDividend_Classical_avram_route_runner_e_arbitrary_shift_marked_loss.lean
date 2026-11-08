-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_e_arbitrary_shift_marked_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:46:47.859537+00:00
-- url     : https://prove2.me/submissions/000f976a-05b8-4b0f-a82e-4b8044e3e421

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_measurable_mark_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_shifted_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s T : ℝ≥0) (k : ℕ) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          (X.X (s + u) ω - X.X s ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (X.X (s + u) ω - X.X s ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ s + T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  let Y : ℝ≥0 → ℝ := fun u => X.X (s + u) ω - X.X s ω
  let μ : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          (X.X (s + u) ω - X.X s ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (X.X (s + u) ω - X.X s ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))
  let ν : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let g : ℝ → ℝ≥0∞ :=
    fun y => if y < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-y) else 0
  have hg : Measurable g := by
    dsimp [g]
    have hs : MeasurableSet {y : ℝ | y < -(1 / ((k : ℝ) + 1))} :=
      measurableSet_lt measurable_id measurable_const
    have hv : Measurable (fun y : ℝ => ENNReal.ofReal (-y)) := by fun_prop
    exact hv.ite hs measurable_const
  have hmap : Measurable (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)) := by
    simpa only [Y] using
      (avram_bv_jump8_turn14_original_shifted_mark_map_measurable X ω s)
  have hRect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 T ×ˢ B) = ν (Ioc s (s + T) ×ˢ B) := by
    intro B hB
    have hgeneric := avram_bv_jump8_generic_measurable_mark_rectangle_encard
      Y hmap 0 T B hB
    have hsource :=
      avram_wave5_01_actual_source_futurepath_marked_count_transport
        X ω s T B hB
    calc
      μ (Ioc 0 T ×ˢ B) =
          ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
            Y u - Function.leftLim Y u ≠ 0 ∧
            Y u - Function.leftLim Y u ∈ B}).encard := by
          change μ (Ioc 0 T ×ˢ B) =
            ({u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
              Y u - Function.leftLim Y u ≠ 0 ∧
              Y u - Function.leftLim Y u ∈ B}).encard at hgeneric
          have hSet :
              {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
                Y u - Function.leftLim Y u ≠ 0 ∧
                Y u - Function.leftLim Y u ∈ B} =
              {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
                Y u - Function.leftLim Y u ≠ 0 ∧
                Y u - Function.leftLim Y u ∈ B} := by
            ext u
            constructor
            · rintro ⟨hu, _, huT, hj, hm⟩
              exact ⟨hu, huT, hj, hm⟩
            · rintro ⟨hu, huT, hj, hm⟩
              exact ⟨hu, hu, huT, hj, hm⟩
          rw [hSet] at hgeneric
          exact hgeneric
      _ = ν (Ioc s (s + T) ×ˢ B) := by
          simpa only [Y, ν] using hsource.symm
  have h := avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
    μ ν s T g hg hRect
  simpa only [μ, ν, g, ite_and] using h
