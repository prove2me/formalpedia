-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_diffuse_mark_open_sample_le_closed_contact_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:06:47.503213+00:00
-- url     : https://prove2.me/submissions/d2607c90-692b-48ec-ba46-1454e0d38f6d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- An open-cap sampled loss is bounded above by the closed-cap limit loss. -/
theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (s : Set ℝ) (hs : IsCompact s)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C})
    (hneg : ∀ b ∈ s, (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, ∀ b ∈ s, |a - b| < δ →
      (if 0 < a ∧ ENNReal.ofReal a < C then
        -(∫ z in Iio (0 : ℝ), w (a + z) - w a ∂ν) else 0) ≤
      -(∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) + ε := by
  let R : ℝ → ℝ := fun b => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν
  have hUC : UniformContinuousOn R s :=
    avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
      C hFinite w hw_cont hw_neg hw_meas ν hνfinite hνatom s hs hsCap
  obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuousOn_iff.mp hUC) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha b hb hab
  have hdist : dist (R a) (R b) < ε :=
    hclose a ha b hb (by simpa [Real.dist_eq] using hab)
  have hdiff : R b - R a < ε := by
    have h := (abs_lt.mp (by simpa [Real.dist_eq] using hdist)).1
    linarith
  change (if 0 < a ∧ ENNReal.ofReal a < C then -R a else 0) ≤ -R b + ε
  split_ifs with hinside
  · linarith
  · have hbneg : R b ≤ 0 := hneg b hb
    linarith
