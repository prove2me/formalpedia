-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_rightpayment_summable_for_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:06:11.458326+00:00
-- url     : https://prove2.me/submissions/c7e2210e-9758-40c7-8c8e-f1a724070259

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Absolute summability of the exact stopped right-dividend remainder in the
post-X, pre-D `riskProcess` convention used by the full Stieltjes theorem. -/
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
    Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) := by
  have hbase :=
    avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
      X x q hq D hD w hjump ω T B hBExact K hK hLocalSecant
  dsimp only at hbase
  have hEq :
      (fun t : B =>
        Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            w (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            w (riskProcess X x D (t : ℝ≥0) ω))) =
      (fun t : B =>
        Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
            w (riskProcess X x D (t : ℝ≥0) ω))) := by
    funext t
    have hs : riskProcess X x D (t : ℝ≥0) ω -
        (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) =
        x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω := by
      simp only [riskProcess]
      ring
    rw [hs]
  rw [hEq]
  exact hbase.1
