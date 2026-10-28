-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_self_convolution_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:42:54.645037+00:00
-- url     : https://prove2.me/submissions/6bd6741c-6954-4296-b5dc-defe0cad7704

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The causal self-convolution of an unbounded-variation q-scale function
is strictly positive at every positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ x : ℝ, 0 < x →
      0 < ∫ s in Ioc (0 : ℝ) x, W s * W (x - s) := by
  intro x hx
  have hLeft : ContinuousOn W (Icc (0 : ℝ) x) :=
    hW.2.2.1.mono (by intro s hs; exact hs.1)
  have hRight : ContinuousOn (fun s : ℝ => W (x - s))
      (Icc (0 : ℝ) x) :=
    hW.2.2.1.comp
      (continuous_const.sub continuous_id).continuousOn
      (by intro s hs; exact sub_nonneg.mpr hs.2)
  have hFcont : ContinuousOn (fun s : ℝ => W s * W (x - s))
      (Icc (0 : ℝ) x) := hLeft.mul hRight
  rw [← intervalIntegral.integral_of_le hx.le]
  apply intervalIntegral.integral_pos hx hFcont
  · intro s hs
    exact mul_nonneg (hW.2.1 s hs.1.le)
      (hW.2.1 (x - s) (sub_nonneg.mpr hs.2))
  · refine ⟨x / 2, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · apply mul_pos
      · exact scaleFunction_strict_pos_of_unbounded_variation
          X q W hW hnbv (x / 2) (by linarith)
      · exact scaleFunction_strict_pos_of_unbounded_variation
          X q W hW hnbv (x - x / 2) (by linarith)
