-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:41:27.138046+00:00
-- url     : https://prove2.me/submissions/3eb6675a-7eab-4c6d-acb4-35fe43049847

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual localised clock reward satisfies the initial secant bound
at zero, including the full physical right-dividend atom at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hF : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hZero : σ ω = 0) : F ω ≤ w x := by
  let W : Ω → ℝ := fun ω =>
    if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (σ ω) ω - rightLimit D (σ ω) ω
    else riskProcess X x D (σ ω) ω
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    Real.exp (-(q * (σ ω : ℝ))) * w (W ω)
  have hBudget : Term ω + Cash ω ≤ w x :=
    avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
      X x q w C D hD hjump σ W Cash Term
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ω hZero
  have heq : F ω = Term ω + Cash ω := by
    rw [hF ω]
  exact heq.le.trans hBudget
