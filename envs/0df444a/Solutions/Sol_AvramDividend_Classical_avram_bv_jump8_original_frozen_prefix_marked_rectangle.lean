-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_marked_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:18:11.300301+00:00
-- url     : https://prove2.me/submissions/9bdc21cd-2352-4c6e-a312-834168330d61

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_marked_window_count_congr
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_mark_maps_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_jump_delta_agree
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X (min u (n : ℝ≥0)) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X (min u (n : ℝ≥0)) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ B) := by
  let f : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
    (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let g : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
    (u, X.X (min u (n : ℝ≥0)) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u)
  let S : Set ℝ≥0 := {u | 0 < u ∧ (f u).2 ≠ 0}
  let T : Set ℝ≥0 := {u | 0 < u ∧ (g u).2 ≠ 0}
  have hMaps : Measurable f ∧ Measurable g :=
    avram_bv_jump8_original_frozen_mark_maps_measurable X ω n
  have hc := avram_bv_jump8_generic_marked_window_count_congr
    S T f g hMaps.1 hMaps.2 n B hB
    (fun u => rfl) (fun u => rfl)
    (by
      intro u hu huN
      have hd := avram_bv_jump8_original_frozen_prefix_jump_delta_agree
        X ω n u hu huN
      have hmark : (f u).2 = (g u).2 := hd
      change (0 < u ∧ (f u).2 ≠ 0) ↔ (0 < u ∧ (g u).2 ≠ 0)
      constructor
      · rintro ⟨_, hs⟩
        exact ⟨hu, by rw [← hmark]; exact hs⟩
      · rintro ⟨_, hs⟩
        exact ⟨hu, by rw [hmark]; exact hs⟩)
    (by
      intro u hu huN
      have hd := avram_bv_jump8_original_frozen_prefix_jump_delta_agree
        X ω n u hu huN
      exact congrArg (fun z : ℝ => (u, z)) hd)
  simpa only [S, T, f, g] using hc
