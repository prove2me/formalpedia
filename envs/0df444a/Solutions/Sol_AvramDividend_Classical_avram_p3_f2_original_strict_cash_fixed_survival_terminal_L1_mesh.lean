-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_strict_cash_fixed_survival_terminal_L1_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:38:10.787935+00:00
-- url     : https://prove2.me/submissions/ccf82c64-73cc-4f25-af33-3d4492a38ec5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical strict-survival terminal is fixed while source cash meshes
increase to the horizon, so the same original cash L1 error controls both
full stopped payoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    let Cash : ℝ → Ω → ℝ := fun r ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0
    Tendsto (fun n => ∫ ω : Ω,
      |(Cash (S : ℝ) ω + Term ω) - (Cash (u n) ω + Term ω)| ∂P)
      atTop (nhds 0) := by
  have hcancel (a b c : ℝ) : (a + c) - (b + c) = a - b := by
    ring
  simpa only [hcancel] using
    (avram_p3_bv_original_strict_cash_cofinal_L1_error_tendsto_zero
      X x C D hD q hq S u hmono hu hbelow hcover)
