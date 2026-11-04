-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:45:47.453338+00:00
-- url     : https://prove2.me/submissions/7d06cdd2-61de-443b-8b4c-503e59501213

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Every strictly positive original right-payment lies in the true atomic carrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hPos : ∀ i, 0 < rightLimit D (t i) ω - D (t i) ω)
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    Summable (fun i : ι => |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ∧
    (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ≤
      (K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by
  let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  obtain ⟨A, hCount, hSupp, hEvery⟩ :=
    avram_p4_d_dividend_original_injective_true_rightjump_absolute_le_full_cash_strong_carrier
      X x q hq D hD w hjump t ω T hT hPre hPay K hK hLocalSecant
  obtain ⟨A₀, μdiffuse, hCount₀, hMeas₀, hNull, hAtom, hCover, hSplit, hBound⟩ :=
    avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
      X x q hq D hD ω T
  have hInA : ∀ i : ι, (t i : ℝ) ∈ A := by
    intro i
    apply hSupp
    have hMass : μ {(t i : ℝ)} =
        ENNReal.ofReal (rightLimit D (t i) ω - D (t i) ω) :=
      hAtom (t i) (hT i)
    rw [hMass]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hPos i))
  exact hEvery hInA hInj
