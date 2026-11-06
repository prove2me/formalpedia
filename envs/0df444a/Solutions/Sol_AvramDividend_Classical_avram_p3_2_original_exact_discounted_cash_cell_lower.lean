-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_exact_discounted_cash_cell_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:14:26.502402+00:00
-- url     : https://prove2.me/submissions/f63eb80c-e4a4-4dc0-a81e-826cb6598df9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_right_endpoint_cash_lintegral_lower
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_restrict_association

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original once-discounted Stieltjes cash on a stopped
grid cell dominates the unweighted physical cash mass discounted at
the right endpoint. This is the finite-grid Fatou lower approximant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  have hMass :=
    avram_p3_2_original_stopped_cash_restrict_association
      X x D ω T m i (fun _ => (1 : ℝ≥0∞))
  have hDisc :=
    avram_p3_2_original_stopped_cash_restrict_association
      X x D ω T m i (fun t =>
        ENNReal.ofReal (Real.exp (-(q * t))))
  have hBound :=
    avram_p3_2_original_right_endpoint_cash_lintegral_lower
      X x D ω q hq T m i
  change ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  rw [hMass, hDisc]
  exact hBound
