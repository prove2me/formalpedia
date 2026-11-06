-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_cap_linear_discounted_source_product_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:12:21.095296+00:00
-- url     : https://prove2.me/submissions/8bdb522a-8956-4d41-a104-cac778ae5652

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_discounted_full_grid_product_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let e : ℕ → ℝ := fun i =>
      Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 ≤
      (∑ i ∈ Finset.range n, e i * source i) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro htop z
    simp [V, htop]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro hnot z
    simp [V, hnot]
  exact avram_p3_c_bvchain_original_discounted_full_grid_product_budget
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω q hq u n hGrid hPre
