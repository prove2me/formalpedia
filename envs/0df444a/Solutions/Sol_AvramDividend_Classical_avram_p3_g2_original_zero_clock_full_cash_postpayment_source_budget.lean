-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_zero_clock_full_cash_postpayment_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:31:38.731765+00:00
-- url     : https://prove2.me/submissions/33421678-2674-4a30-b9d3-68dcdb8473dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original zero clock includes the time-zero right dividend exactly once.
Actual capped BV admissibility and the C1 gradient discharge postpayment
nonnegativity; the terminal disappears on immediate ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (0 : ℝ≥0∞) < ruinTime X x D ω then
      w (x + X.X 0 ω - rightLimit D 0 ω)
     else 0) ≤ w x := by
  have hpost : ∀ ξ, 0 ≤ w (x - rightLimit D 0 ξ) := by
    intro ξ
    have hn :=
      avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
        X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD ξ 0
    simpa only [X.X_zero ξ, add_zero] using hn
  have hzero :=
    avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise
      X x q D hD.1.1 w hjump hpost ω
  simpa only [X.X_zero ω, add_zero, max_eq_right (hpost ω)] using hzero
