-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_frozen_prefix_general_mark_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:17:41.048198+00:00
-- url     : https://prove2.me/submissions/f467157d-21b3-4231-8456-60f32301cc99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_mark_maps_any_horizon
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_generic_marked_window_count_any_horizon
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u)))) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let ν : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X (min u T) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X (min u T) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u))
  have hrect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 T ×ˢ B) = ν (Ioc 0 T ×ˢ B) := by
    intro B hB
    let f : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let h : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
      (u, X.X (min u T) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u)
    let S : Set ℝ≥0 := {u | 0 < u ∧ (f u).2 ≠ 0}
    let U : Set ℝ≥0 := {u | 0 < u ∧ (h u).2 ≠ 0}
    have hMaps := avram_route_runner_f_original_frozen_mark_maps_any_horizon X ω T
    have hmark (u : ℝ≥0) (hu : 0 < u) (huT : u ≤ T) :
        (f u).2 = (h u).2 := by
      change X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u =
        X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u
      rw [min_eq_left huT,
        avram_wave7_06_original_frozen_prefix_leftLim_before_stop X ω T u hu huT]
    have hc := avram_route_runner_f_generic_marked_window_count_any_horizon
      S U f h hMaps.1 hMaps.2 T B hB
      (fun _ => rfl) (fun _ => rfl)
      (by
        intro u hu huT
        have hd := hmark u hu huT
        change (0 < u ∧ (f u).2 ≠ 0) ↔ (0 < u ∧ (h u).2 ≠ 0)
        constructor
        · rintro ⟨_, hs⟩
          exact ⟨hu, by rw [← hd]; exact hs⟩
        · rintro ⟨_, hs⟩
          exact ⟨hu, by rw [hd]; exact hs⟩)
      (by
        intro u hu huT
        exact congrArg (fun z : ℝ => (u, z)) (hmark u hu huT))
    simpa only [S, U, f, h, μ, ν] using hc
  have hw := avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
    μ ν 0 T g hg (by intro B hB; simpa only [zero_add] using hrect B hB)
  simpa [μ, ν] using hw
