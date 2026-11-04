-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:16:17.242189+00:00
-- url     : https://prove2.me/submissions/8de196d9-f510-4f0b-9527-287762132d71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_initial_discounted_product_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
/-- Original closed interior cells with a strict-open prepayment final cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ, V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n → (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i => V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let finalCash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo (u n : ℝ) (b : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) + finalCash +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) - V (x + X.X (u n) ω - rightLimit D (u n) ω)) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) +
      (Real.exp (-(q * (b : ℝ))) - e n) * w (riskProcess X x D b ω) := by
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let cash : ℕ → ℝ := fun i => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
    Ioc (u i : ℝ) (u (i + 1) : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i => V (x + X.X (u i) ω - rightLimit D (u i) ω)
  let source : ℕ → ℝ := fun i => V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  let finalCash : ℝ := (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (u n : ℝ) (b : ℝ),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  change rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) + finalCash +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) - V (x + X.X (u n) ω - rightLimit D (u n) ω)) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) +
      (Real.exp (-(q * (b : ℝ))) - e n) * w (riskProcess X x D b ω)
  have hBook := avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w X x C hC hxc w V hVtop hVfinite D hD
  have hVb := (hBook ω b).1
  have hVn := (hBook ω (u n)).2
  have hOld := avram_p3_c_bvchain_original_initial_discounted_product_source_budget
    X x C hC hxc w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD hjump ω q hq u n hzero hGrid hPre
  have hLast := avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD ω q hq (u n) b hFinal hBPre
  change finalCash + e n * (V (riskProcess X x D b ω) - V (x + X.X b ω - rightLimit D (u n) ω)) ≤ 0 at hLast
  rw [hVb] at hLast
  change rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) +
      e n * w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) at hOld
  rw [hVn]
  nlinarith only [hOld, hLast]
