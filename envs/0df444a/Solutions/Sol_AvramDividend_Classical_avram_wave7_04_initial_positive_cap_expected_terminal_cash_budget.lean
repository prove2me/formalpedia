-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_04_initial_positive_cap_expected_terminal_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:48:05.131169+00:00
-- url     : https://prove2.me/submissions/824317d0-1772-40e0-b221-8508a1fa8c00

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_positive_cap_full_atom_terminal_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ)
    (hCashI : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hTermI : Integrable (fun ω : Ω =>
      if (0 : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (w (x - rightLimit D 0 ω)) else 0) P) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, if (0 : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (w (x - rightLimit D 0 ω)) else 0 ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    if (0 : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (w (x - rightLimit D 0 ω)) else 0
  have hPath : ∀ ω, Cash ω + Term ω ≤ w x := by
    intro ω
    exact avram_wave7_04_initial_positive_cap_full_atom_terminal_budget
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD hjump q ω
  have hMean :
      (∫ ω, Cash ω + Term ω ∂P) ≤ ∫ ω, w x ∂P :=
    integral_mono (hCashI.add hTermI) (integrable_const _) hPath
  change (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) ≤ w x
  calc
    (∫ ω, Cash ω ∂P) + (∫ ω, Term ω ∂P) =
        (∫ ω, Cash ω + Term ω ∂P) :=
      (integral_add hCashI hTermI).symm
    _ ≤ (∫ ω, w x ∂P) := hMean
    _ = w x := by simp
