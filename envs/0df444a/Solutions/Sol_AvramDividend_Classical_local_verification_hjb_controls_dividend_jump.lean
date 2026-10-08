-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_hjb_controls_dividend_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:31:50.504992+00:00
-- url     : https://prove2.me/submissions/cd74adb8-7cd3-4100-a00f-4c895a517c9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_smooth_differentiable
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_derivative_ge_one_implies_value_drop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (u d : ℝ) (hd : 0 ≤ d) (hcap : d ≤ u)
    (huC : ENNReal.ofReal u < C) :
    d ≤ w u - w (u - d) := by
  have ha : 0 ≤ u - d := sub_nonneg.mpr hcap
  have hab : u - d ≤ u := sub_le_self u hd
  have hcont : ContinuousOn w (Icc (u - d) u) := by
    refine hw_cont.mono ?_
    intro z hz
    exact ha.trans hz.1
  have hdiff : DifferentiableOn ℝ w (Ioo (u - d) u) := by
    apply (local_verification_smooth_differentiable X w C hw_smooth).mono
    intro z hz
    exact ⟨ha.trans_lt hz.1,
      (ENNReal.ofReal_le_ofReal hz.2.le).trans_lt huC⟩
  have hgrad : ∀ z ∈ Ioo (u - d) u, 1 ≤ deriv w z := by
    intro z hz
    have hzPos : 0 < z := ha.trans_lt hz.1
    have hzCap : ENNReal.ofReal z < C :=
      (ENNReal.ofReal_le_ofReal hz.2.le).trans_lt huC
    exact (local_verification_hjb_implies_components
      X q w C hw_hjb z hzPos hzCap).2.2
  have hbound :=
    derivative_ge_one_implies_value_drop w (u - d) u hab hcont hdiff hgrad
  linarith
