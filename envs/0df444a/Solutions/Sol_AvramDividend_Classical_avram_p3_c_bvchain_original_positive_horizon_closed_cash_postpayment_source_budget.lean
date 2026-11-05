-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_positive_horizon_closed_cash_postpayment_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:51:02.841866+00:00
-- url     : https://prove2.me/submissions/c055c11a-7d2b-40d7-97b9-a8e7836aeb51

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_strict_P3_cash_frozen_source_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Closed-horizon original cash and post-rightpayment terminal dominated by frozen source. -/
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
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i < u (i + 1))
    (hPre : ∀ i : ℕ, i < n → (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) *
        w (riskProcess X x D b ω - (rightLimit D b ω - D b ω)) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) := by
  have hStrict := avram_p3_c_bvchain_original_literal_strict_P3_cash_frozen_source_grid_budget
    X x hx C hC hxc w V hw0 hw_cont hw_neg hw_smooth hw_grad hVtop hVfinite
    D hD hjump ω q hq u n hzero hGrid hPre b hFinal hBPre
  have hSplit := avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
    X x C D hD ω q hq b
  have hAtom := avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
    X x D hD.1.1 w hjump ω b (Or.inr hBPre) q
  dsimp only at hStrict ⊢
  rw [hSplit]
  calc
    _ = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        ((∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (b : ℝ)) ∩
            ({(b : ℝ)} : Set ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          Real.exp (-(q * (b : ℝ))) *
            w (riskProcess X x D b ω - (rightLimit D b ω - D b ω))) := by rw [add_assoc]
    _ ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) :=
      add_le_add_right hAtom _
    _ ≤ _ := hStrict
