-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:32:54.022404+00:00
-- url     : https://prove2.me/submissions/23560226-58fc-45f4-9a56-e5951fa871fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original signed right-dividend remainder has a stopped cash envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤
        w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω -
            (rightLimit D s ω - D s ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (K : ℝ) (hK : 1 ≤ K)
    (hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω)))
    (hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          K * (rightLimit D (t i) ω - D (t i) ω)) :
    Summable (fun i : ι =>
      |Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))|) ∧
    (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ≤
      (∑' i : ι, (K - 1) *
        (Real.exp (-(q * (t i : ℝ))) *
          (rightLimit D (t i) ω - D (t i) ω))) := by
  obtain ⟨hSignedSummable, _⟩ :=
    avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
      X x D w q hjump t ω hPre K hK hPayNonneg hPaySummable hLocalSecant
  have hAbsSummable := hSignedSummable.abs
  have hEnvelopeSummable : Summable (fun i : ι =>
      (K - 1) * (Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) :=
    hPaySummable.mul_left (K - 1)
  have hBound (i : ι) :
      |Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))| ≤
      (K - 1) * (Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω)) := by
    have he : 0 ≤ Real.exp (-(q * (t i : ℝ))) := (Real.exp_pos _).le
    have hNeg :=
      avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
        X x D w q hjump (fun _ => t i) ω (hPre i)
    calc
      _ = -(Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) := abs_of_nonpos hNeg
      _ = Real.exp (-(q * (t i : ℝ))) *
        ((w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω)) -
          (rightLimit D (t i) ω - D (t i) ω)) := by ring
      _ ≤ Real.exp (-(q * (t i : ℝ))) *
        (K * (rightLimit D (t i) ω - D (t i) ω) -
          (rightLimit D (t i) ω - D (t i) ω)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right (hLocalSecant i) _) he
      _ = (K - 1) * (Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω)) := by ring
  exact ⟨hAbsSummable, hAbsSummable.tsum_le_tsum hBound hEnvelopeSummable⟩