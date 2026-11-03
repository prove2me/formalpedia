-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:36:54.510674+00:00
-- url     : https://prove2.me/submissions/61d1c7a5-2e46-40e0-ab2c-8cccf14dd9f4

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

/-- The actual positive cap C1 HJB gradient and nonnegative zero boundary force nonnegative candidate value on every compact positive interval below the cap. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∀ y ∈ Icc (0 : ℝ) b, 0 ≤ w y := by
  have hSub : Ioo (0 : ℝ) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro z hz
    exact ⟨hz.1, (ENNReal.ofReal_mono hz.2.le).trans_lt hbC⟩
  have hDiff : DifferentiableOn ℝ w (interior (Icc (0 : ℝ) b)) := by
    have hC1 : ContDiffOn ℝ 1 w (Ioo (0 : ℝ) b) :=
      hw_smooth.mono hSub
    have hD := hC1.differentiableOn (by norm_num)
    exact hD.mono (by
      intro z hz
      simpa only [interior_Icc] using hz)
  have hCont : ContinuousOn w (Icc (0 : ℝ) b) :=
    hw_cont.mono (by
      intro z hz
      exact hz.1)
  have hDeriv : ∀ z ∈ interior (Icc (0 : ℝ) b),
      0 ≤ deriv w z := by
    intro z hz
    have hzIoo : z ∈ Ioo (0 : ℝ) b := by
      simpa only [interior_Icc] using hz
    exact (zero_le_one.trans
      (hw_grad z hzIoo.1 (hSub hzIoo).2))
  have hMono : MonotoneOn w (Icc (0 : ℝ) b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) b) hCont hDiff hDeriv
  intro y hy
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) b :=
    ⟨le_refl _, hb⟩
  exact hw0.trans (hMono h0 hy hy.1)