-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_positive_horizon_true_cash_single_source_increment_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:04:06.572087+00:00
-- url     : https://prove2.me/submissions/ca837065-2fd5-46b7-ad9f-5464ee464b4e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original source-frozen BV budget on the coarsest positive pre-ruin mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0) (hb : 0 < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D 0 ω +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (0 : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (V (x + X.X b ω - rightLimit D 0 ω) -
        V (x + X.X 0 ω - rightLimit D 0 ω)) := by
  let u : ℕ → ℝ≥0 := fun _ => 0
  have hzero : u 0 = 0 := rfl
  have hGrid : ∀ i : ℕ, i < 0 → u i < u (i + 1) := by
    intro i hi
    exact (Nat.not_lt_zero _ hi).elim
  have hPre : ∀ i : ℕ, i < 0 → (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    exact (Nat.not_lt_zero _ hi).elim
  have hBudget := avram_p3_c_bvchain_original_strict_horizon_true_cash_frozen_source_budget
    X x hx C hC hxc w V hw0 hw_cont hw_neg hw_smooth hw_grad hVtop hVfinite
    D hD hjump ω q hq u 0 hzero hGrid hPre b hb hBPre
  simpa [u] using hBudget
