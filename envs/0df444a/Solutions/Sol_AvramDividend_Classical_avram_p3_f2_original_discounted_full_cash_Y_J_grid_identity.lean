-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_full_cash_Y_J_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:58:04.276606+00:00
-- url     : https://prove2.me/submissions/9c8057b4-b8c9-4cdb-ba59-678a2d6857b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The literal original discounted Stieltjes cash grid splits its frozen X term into Y and J. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Set.Ioc (u i : ℝ) (u (i + 1) : ℝ),
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
      (∑ i ∈ Finset.range n, e i *
        ((w (z i + c i - j i) - w (z i - j i)) +
         (w (z i - j i) - w (z i)))) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i := by
  intro J Y z c j e cash post frozen rem
  have hProduct :=
    avram_p3_c_bvchain_original_exact_discounted_product_remainder_identity
      X x D w q ω u n
  have hSplitSum :
      (∑ i ∈ Finset.range n, e i * frozen i) =
      (∑ i ∈ Finset.range n, e i *
        ((w (z i + c i - j i) - w (z i - j i)) +
          (w (z i - j i) - w (z i)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun v : ℝ => e i * v)
      (avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
        X x C D hD w ω u n i (Finset.mem_range.mp hi))
  calc
    (∑ i ∈ Finset.range n, cash i) +
      e n * post n - e 0 * post 0 =
      (∑ i ∈ Finset.range n, e i * frozen i) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i := hProduct
    _ = (∑ i ∈ Finset.range n, e i *
        ((w (z i + c i - j i) - w (z i - j i)) +
          (w (z i - j i) - w (z i)))) +
      (∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1)) +
      ∑ i ∈ Finset.range n, rem i := by rw [hSplitSum]
