-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_weighted_source_product_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:08:55.177011+00:00
-- url     : https://prove2.me/submissions/e3741952-2047-4e67-adaf-ecc38f880d7a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Weighted original source-and-dividend discrete integration by parts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
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
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < n → 0 ≤ r (i + 1)) :
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
      r n * post n - r 0 * post 0 ≤
      (∑ i ∈ Finset.range n, r (i + 1) * source i) +
      ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by
  classical
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i =>
    w (x + X.X (u i) ω - rightLimit D (u i) ω)
  let source : ℕ → ℝ := fun i =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
  change (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
      r n * post n - r 0 * post 0 ≤
      (∑ i ∈ Finset.range n, r (i + 1) * source i) +
        ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i
  have hcell (i : ℕ) (hi : i < n) :
      cash i + post (i + 1) - post i ≤ source i := by
    have hMass :=
      avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
        X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
        D hD ω (u i) (u (i + 1)) (hGrid i hi) (Or.inr (hPre i hi))
    have hNonneg : 0 ≤
        (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal :=
      ENNReal.toReal_nonneg
    have hDrop :
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) ≤ 0 := by
      linarith only [hMass, hNonneg]
    have hDisc :=
      avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
        X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
        D hD ω q hq (u i) (u (i + 1)) (hGrid i hi) (hPre i hi)
    have hFactor :
        Real.exp (-(q * (u i : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hqti : 0 ≤ q * (u i : ℝ) :=
        mul_nonneg hq (NNReal.coe_nonneg (u i))
      linarith only [hqti]
    have hExtra :
        (1 - Real.exp (-(q * (u i : ℝ)))) *
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
            V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hFactor) hDrop
    have hRaw :
        cash i +
          V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) ≤ 0 := by
      dsimp [cash] at hDisc ⊢
      nlinarith only [hDisc, hExtra]
    have hPostA := (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
      X x C hC hxc w V hVtop hVfinite D hD ω (u i)).2
    have hPostB := (avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
      X x C hC hxc w V hVtop hVfinite D hD ω (u (i + 1))).2
    dsimp [post, source]
    rw [← hPostA, ← hPostB]
    linarith only [hRaw]
  have hweighted (i : ℕ) (hi : i < n) :
      r (i + 1) * cash i +
        r (i + 1) * post (i + 1) -
          r (i + 1) * post i ≤ r (i + 1) * source i := by
    have h := mul_le_mul_of_nonneg_left (hcell i hi) (hr i hi)
    nlinarith only [h]
  have hs :
      (∑ i ∈ Finset.range n,
        (r (i + 1) * cash i +
          r (i + 1) * post (i + 1) -
            r (i + 1) * post i)) ≤
        ∑ i ∈ Finset.range n, r (i + 1) * source i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hweighted i (Finset.mem_range.mp hi)
  have htel (k : ℕ) :
      (∑ i ∈ Finset.range k, r (i + 1) * post (i + 1)) -
          (∑ i ∈ Finset.range k, r (i + 1) * post i) =
        r k * post k - r 0 * post 0 -
          ∑ i ∈ Finset.range k, (r (i + 1) - r i) * post i := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_range_succ]
      linear_combination ih
  have hid :
      (∑ i ∈ Finset.range n, r (i + 1) * cash i) +
          r n * post n - r 0 * post 0 =
        (∑ i ∈ Finset.range n,
          (r (i + 1) * cash i +
            r (i + 1) * post (i + 1) -
              r (i + 1) * post i)) +
          ∑ i ∈ Finset.range n, (r (i + 1) - r i) * post i := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith only [htel n]
  rw [hid]
  linarith only [hs]
