-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_interior_diffuse_countable_atomic_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:20:41.075798+00:00
-- url     : https://prove2.me/submissions/beaebc85-64a5-4e4c-b6b7-a97f90604a26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original-source signed mixed dividend remainder on a verified strict
interior payment region plus an arbitrary summable family of actual right jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hInt : IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      A (dividendMeasure D ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (t : ι → ℝ≥0)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω)))) :
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω))
      ∂(dividendMeasure D ω)) +
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by
  have hDiffuse :
      (∫ s in A, Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω))
        ∂(dividendMeasure D ω)) ≤ 0 :=
    avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
      X x D hD q w C hw_grad ω A hA hregion hInt
  have hAtoms :
      (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ≤ 0 := by
    apply tsum_nonpos
    intro i
    exact avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => t i) ω (hPre i)
  exact add_nonpos hDiffuse hAtoms