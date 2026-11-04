-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_positive_atom_full_signed_and_absolute_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:59:15.266818+00:00
-- url     : https://prove2.me/submissions/607931f2-61a2-4d5c-a753-e3e6e3c764cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_signed_tsum_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- A real signed original atomic control remainder, with no carrier membership premise. -/
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
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧
      (∑' i : ι, |J i|) ≤
        (K - 1) * (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by
  let μ : Measure ℝ := (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
    ((rightLimit D (t i) ω - D (t i) ω) +
      w (x + X.X (t i) ω - rightLimit D (t i) ω) -
      w (riskProcess X x D (t i) ω))
  obtain ⟨hAbs, hAbsBound⟩ :=
    avram_p4_d_dividend_original_positive_rightjump_absolute_fullcash_no_carrier_premise
      X x q hq D hD w hjump t ω T hT hPre hPay hPos hInj K hK hLocalSecant
  have hSigned : Summable J := hAbs.of_abs
  have hNonpos : (∑' i : ι, J i) ≤ 0 :=
    avram_p4_d_dividend_original_countable_rightjump_signed_tsum_nonpos
      X x D w q hjump t ω hPre hSigned
  exact ⟨hSigned, hNonpos, hAbs, hAbsBound⟩
