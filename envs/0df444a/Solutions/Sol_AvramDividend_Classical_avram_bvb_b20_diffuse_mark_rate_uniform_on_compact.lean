-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:56:49.152914+00:00
-- url     : https://prove2.me/submissions/7200e66e-30a9-4d17-a235-34f442406f5d

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
    (s : Set ℝ) (hs : IsCompact s)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    UniformContinuousOn
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) s := by
  apply hs.uniformContinuousOn_of_continuous
  intro b hb
  have hbc := hsCap hb
  exact
    (avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
      C hFinite w hw_cont hw_neg hw_meas ν hνfinite hνatom b hbc.1 hbc.2).mono hsCap
