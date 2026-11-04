-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_discounted_full_grid_product_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:27:45.969193+00:00
-- url     : https://prove2.me/submissions/46708a43-2608-41df-acde-8bf2923964a5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_discount_left_full_measure_le
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Actual original full-grid discounted BV source/product budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
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
  classical
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
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
  change (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 ≤
      (∑ i ∈ Finset.range n, e i * source i) +
        ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hcell (i : ℕ) (hi : i < n) :
      cash i + e i * post (i + 1) - e i * post i ≤
        e i * source i := by
    have hInclude : Ioc (u i : ℝ) (u (i + 1) : ℝ) ⊆
        paymentTimes (ruinTime X x D ω) := by
      apply paymentTimes_Ioc_subset_of_terminal_survival
      · exact (u i).property
      · simpa using (hPre i hi)
    have hSet : paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ) =
          Ioc (u i : ℝ) (u (i + 1) : ℝ) := by
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro ht
        exact ⟨hInclude ht, ht⟩
    have hFinite :
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          dividendMeasure D ω
            (Ioc (u i : ℝ) (u (i + 1) : ℝ)) ≠ ⊤ := by
      rw [dividendMeasure_Ioc_rightLimit D hStrategy ω
        (u i) (u (i + 1))]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hCash := avram_p3_c_bvchain_public_discount_left_full_measure_le
      q hq (dividendMeasure D ω) (u i : ℝ) (u (i + 1) : ℝ)
    have hCashReal := ENNReal.toReal_mono hFinite hCash
    have hExpNonneg : 0 ≤ Real.exp (-(q * (u i : ℝ))) :=
      (Real.exp_pos _).le
    have hCashScaled : cash i ≤
        e i * (dividendMeasure D ω
          (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal := by
      dsimp only [cash, e]
      rw [hSet]
      simpa only [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hExpNonneg] using hCashReal
    have hDrop :=
      avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
        X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
        D hD ω (u i) (u (i + 1)) (hGrid i hi)
        (Or.inr (hPre i hi))
    have hWeighted := mul_nonpos_of_nonneg_of_nonpos hExpNonneg hDrop
    dsimp only [cash, post, source, e] at *
    rw [hSet] at hCashScaled
    rw [hSet]
    nlinarith only [hCashScaled, hWeighted]
  have hs :
      (∑ i ∈ Finset.range n,
        (cash i + e i * post (i + 1) - e i * post i)) ≤
        ∑ i ∈ Finset.range n, e i * source i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hcell i (Finset.mem_range.mp hi)
  have htel (k : ℕ) :
      (∑ i ∈ Finset.range k, e i * post (i + 1)) -
          (∑ i ∈ Finset.range k, e i * post i) =
        e k * post k - e 0 * post 0 -
          ∑ i ∈ Finset.range k, (e (i + 1) - e i) * post (i + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      linear_combination ih
  have hid :
      (∑ i ∈ Finset.range n, cash i) +
          e n * post n - e 0 * post 0 =
        (∑ i ∈ Finset.range n,
          (cash i + e i * post (i + 1) - e i * post i)) +
          ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    nlinarith only [htel n]
  nlinarith only [hid, hs]
