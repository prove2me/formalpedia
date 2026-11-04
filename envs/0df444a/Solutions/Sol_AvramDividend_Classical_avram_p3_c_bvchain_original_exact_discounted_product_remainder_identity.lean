-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:18:10.692307+00:00
-- url     : https://prove2.me/submissions/2d95a577-0059-48ed-a089-c51a084b3da2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Exact original controlled discounted finite-grid remainder accounting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 =
      (∑ i ∈ Finset.range n, e i * frozen i) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i := by
  classical
  let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i =>
    w (x + X.X (u i) ω - rightLimit D (u i) ω)
  let frozen : ℕ → ℝ := fun i =>
    w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
  let rem : ℕ → ℝ := fun i =>
    cash i + e i * (post (i + 1) - post i - frozen i)
  change (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 =
      (∑ i ∈ Finset.range n, e i * frozen i) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i
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
  have hrem (k : ℕ) :
      (∑ i ∈ Finset.range k, rem i) =
        (∑ i ∈ Finset.range k, cash i) +
          (∑ i ∈ Finset.range k, e i * post (i + 1)) -
          (∑ i ∈ Finset.range k, e i * post i) -
          (∑ i ∈ Finset.range k, e i * frozen i) := by
    simp only [rem, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  rw [hrem n]
  nlinarith only [htel n]
