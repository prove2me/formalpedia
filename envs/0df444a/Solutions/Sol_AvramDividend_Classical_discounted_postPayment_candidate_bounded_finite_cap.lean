-- Prove2me | solution 1 for AvramDividend.Classical.discounted_postPayment_candidate_bounded_finite_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:46:39.442477+00:00
-- url     : https://prove2.me/submissions/d6e963b0-1819-4166-a59e-03f436979364

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPayment_candidate_uniform_upper_bound_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_postPayment_terminal_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω : Ω) (t : ℝ≥0),
      0 ≤ Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω) ∧
      Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω) ≤ B := by
  obtain ⟨B, hBnonneg, hB⟩ :=
    capped_postPayment_candidate_uniform_upper_bound_finite_cap
      X x c hc D hD hxc w hw_cont hw_neg
  refine ⟨B, hBnonneg, ?_⟩
  intro ω t
  have hw : 0 ≤ w (x + X.X t ω - rightLimit D t ω) :=
    local_verification_postPayment_terminal_nonnegative
      X q w (ENNReal.ofReal c) hw_cont hw0 hw_neg
      hw_smooth hw_hjb x hxc D hD ω t
  have hdiscountpos : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    (Real.exp_pos _).le
  have hdiscountle : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    have hqt : 0 ≤ q * (t : ℝ) :=
      mul_nonneg hq.le (NNReal.coe_nonneg t)
    have hnegqt : -(q * (t : ℝ)) ≤ 0 := neg_nonpos.mpr hqt
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hnegqt)
  constructor
  · exact mul_nonneg hdiscountpos hw
  · calc
      Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω) ≤
          1 * w (x + X.X t ω - rightLimit D t ω) :=
        mul_le_mul_of_nonneg_right hdiscountle hw
      _ = w (x + X.X t ω - rightLimit D t ω) := one_mul _
      _ ≤ B := hB ω t
