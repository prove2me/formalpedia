-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_b20_diffuse_finite_mark_rate_uniform_bounded_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:35:50.169646+00:00
-- url     : https://prove2.me/submissions/704d98b9-95d1-42f2-8bfd-90cc046ac1ab

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The uniformly continuous finite-mark potential attains a compact envelope. -/
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
  let f : ℝ → ℝ := fun b => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν
  have huc : UniformContinuousOn f s := by
    exact avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
      C hFinite w hw_cont hw_neg hw_meas ν hνfinite hνatom s hs hsCap
  have hc : ContinuousOn (fun b => |f b|) s := huc.continuousOn.abs
  obtain ⟨a, ha, hmax⟩ := hs.exists_isMaxOn hsNonempty hc
  refine ⟨|f a|, abs_nonneg _, ?_⟩
  intro b hb
  exact hmax hb
