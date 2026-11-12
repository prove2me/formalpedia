-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_diffuse_finite_mark_rate_uniform_bounded_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:32:05.011807+00:00
-- url     : https://prove2.me/submissions/6609af82-d42e-4f2c-8c28-b3254611d04a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (s : Set ℝ) (hs : IsCompact s) (hsNonempty : s.Nonempty)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ s, |∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν| ≤ M := by
  let rate : ℝ → ℝ := fun b => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν
  have hcont : ContinuousOn rate s := by
    intro b hb
    exact
      (avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
        C hFinite w hw_cont hw_neg hw_meas ν hνfinite hνatom
        b (hsCap hb).1 (hsCap hb).2).mono hsCap
  obtain ⟨b0, hb0, hmax⟩ := hs.exists_isMaxOn hsNonempty hcont.abs
  refine ⟨|rate b0|, abs_nonneg _, ?_⟩
  intro b hb
  exact hmax hb
