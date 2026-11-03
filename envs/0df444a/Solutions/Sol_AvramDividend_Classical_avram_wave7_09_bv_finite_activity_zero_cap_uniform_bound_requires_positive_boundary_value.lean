-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_requires_positive_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:28:55.467272+00:00
-- url     : https://prove2.me/submissions/1bdfc81c-abd4-4c16-b847-583220a91236

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- An original finite-activity BV zero-cap strategy cannot have every
finite-horizon complete Stieltjes payout bounded by a nonpositive W. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) :
    0 < W := by
  obtain ⟨n, hn⟩ :=
    avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
      X hX hBV hFinite q hq
  by_contra hW
  have hWle : W ≤ 0 := le_of_not_gt hW
  have hzero : ENNReal.ofReal W = 0 := ENNReal.ofReal_eq_zero.mpr hWle
  have hbound := hUniform n
  rw [hzero] at hbound
  exact (not_le_of_gt hn) hbound
