-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_ubv_C2_stopped_atoms_interior_band_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:38:46.964194+00:00
-- url     : https://prove2.me/submissions/06993605-1b00-4ff6-bfe8-82fd648582ac

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- UBV C² reserve-strip envelope controls original right-payment sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hStates : ∀ i : ι,
      riskProcess X x D (t i) ω ∈ Icc a b ∧
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b)
    (hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by
  have hLip := avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
    C w hwC2 a b hOpen hBand K hK
  have hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          max 1 (K : ℝ) *
            (rightLimit D (t i) ω - D (t i) ω) := by
    intro i
    have hChron :
        riskProcess X x D (t i) ω -
          (x + X.X (t i) ω - rightLimit D (t i) ω) =
            rightLimit D (t i) ω - D (t i) ω := by
      simp only [riskProcess]
      ring
    calc
      w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        |w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω)| :=
        le_abs_self _
      _ ≤ (K : ℝ) *
          |riskProcess X x D (t i) ω -
            (x + X.X (t i) ω - rightLimit D (t i) ω)| :=
        hLip _ (hStates i).1 _ (hStates i).2
      _ = (K : ℝ) *
          (rightLimit D (t i) ω - D (t i) ω) := by
        rw [hChron, abs_of_nonneg (hPayNonneg i)]
      _ ≤ max 1 (K : ℝ) *
          (rightLimit D (t i) ω - D (t i) ω) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 (K : ℝ))
          (hPayNonneg i)
  exact avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
    X x D w q hjump t ω hPre (max 1 (K : ℝ))
    (le_max_left 1 (K : ℝ)) hPayNonneg hPaySummable hLocalSecant