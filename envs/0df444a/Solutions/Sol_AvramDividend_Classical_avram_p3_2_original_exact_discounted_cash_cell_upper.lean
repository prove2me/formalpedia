-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_exact_discounted_cash_cell_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:25:00.151196+00:00
-- url     : https://prove2.me/submissions/ac70d21c-5f00-4b63-a913-47772040f8e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_left_endpoint_cash_lintegral_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_cash_restrict_association

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original once-discounted stopped-cell Stieltjes cash is bounded
above by physical cash multiplied by the left-endpoint discount factor.
Combined with the corresponding right bound, this is the exact mesh squeeze. -/
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
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
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
    avram_p3_2_original_left_endpoint_cash_lintegral_upper
      X x D ω q hq T m i
  change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          (1 : ℝ≥0∞) ∂(dividendMeasure D ω))
  rw [hMass, hDisc]
  exact hBound
