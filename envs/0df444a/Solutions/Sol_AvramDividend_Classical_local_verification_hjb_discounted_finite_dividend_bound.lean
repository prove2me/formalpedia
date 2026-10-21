-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_hjb_discounted_finite_dividend_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T14:57:16.016551+00:00
-- url     : https://prove2.me/submissions/0bdf37c7-05fa-49c8-bb73-6c00acb83eae

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_finite_dividend_telescoping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (u d : ℕ → ℝ) (times : ℕ → ℝ≥0)
    (hupdate : ∀ k : ℕ, u (k + 1) = u k - d k)
    (hpos : ∀ k : ℕ, 0 ≤ d k)
    (hsolv : ∀ k : ℕ, d k ≤ u k)
    (hcap : ∀ k : ℕ, ENNReal.ofReal (u k) ≤ C)
    (n : ℕ) (hterminal : 0 ≤ w (u n)) :
    (∑ k ∈ Finset.range n,
      Real.exp (-(q * (times k : ℝ))) * d k) ≤ w (u 0) := by
  have htel :=
    local_verification_hjb_finite_dividend_telescoping
      X q w C hw_cont hw_smooth hw_hjb
      u d hupdate hpos hsolv hcap n
  have hdiscount :
      (∑ k ∈ Finset.range n,
        Real.exp (-(q * (times k : ℝ))) * d k) ≤
      (∑ k ∈ Finset.range n, d k) := by
    apply Finset.sum_le_sum
    intro k hk
    have ht : 0 ≤ (times k : ℝ) := NNReal.coe_nonneg _
    have hqt : 0 ≤ q * (times k : ℝ) := mul_nonneg hq ht
    have hexp : Real.exp (-(q * (times k : ℝ))) ≤ 1 := by
      have hle : -(q * (times k : ℝ)) ≤ 0 :=
        neg_nonpos.mpr hqt
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
    have hm := mul_le_mul_of_nonneg_right hexp (hpos k)
    simpa only [one_mul] using hm
  linarith
