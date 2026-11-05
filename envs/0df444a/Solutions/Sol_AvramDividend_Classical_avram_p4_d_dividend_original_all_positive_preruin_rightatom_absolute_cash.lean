-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:00:40.102914+00:00
-- url     : https://prove2.me/submissions/6150878d-3059-469c-aa98-fb08fb730b70

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Every original positive right-payment strictly before ruin and through a
closed horizon has an absolutely summable signed secant correction bounded
by the actual stopped Stieltjes Cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ≥0)
    (hBExact : B = {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧ t ≤ T ∧
      0 < rightLimit D t ω - D t ω})
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ t : B,
      w (riskProcess X x D (t : ℝ≥0) ω) -
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) ≤
          K * (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) :
    let J : B → ℝ := fun t => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
        w (riskProcess X x D (t : ℝ≥0) ω))
    Summable J ∧ (∑' t : B, J t) ≤ 0 ∧
      Summable (fun t : B => |J t|) ∧
      (∑' t : B, |J t|) ≤ (K - 1) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  have hBsubset : B ⊆ {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧ t ≤ T ∧
      0 < rightLimit D t ω - D t ω} := by
    intro t ht
    rw [hBExact] at ht
    exact ht
  have hT : ∀ t : B, (t : ℝ≥0) ≤ T := by
    intro t
    have ht := hBsubset t.property
    exact ht.2.2.1
  have hPay : ∀ t : B, ((t : ℝ≥0) : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by
    intro t
    have ht := hBsubset t.property
    have hzero : (0 : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by positivity
    have hru : (0 : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_le_of_lt hzero ht.2.1
    rw [paymentTimes_eq_strict_of_pos _ hru]
    constructor
    · positivity
    · simpa only [ENNReal.ofReal_coe_nnreal] using ht.2.1
  have hInj : Function.Injective (fun t : B => ((t : ℝ≥0) : ℝ)) := by
    intro a b h
    apply Subtype.ext
    exact NNReal.coe_injective h
  exact avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
    X x q hq D hD w hjump (fun t : B => (t : ℝ≥0)) ω T
    hT hPay hInj K hK hLocalSecant
