-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_grid_cap_crossing_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:14:23.199121+00:00
-- url     : https://prove2.me/submissions/3fb21715-8c42-40cd-8e1a-20c93e0326aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (u : ℕ → ℝ≥0) (n : ℕ) :
    ∀ ω,
      let a : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      let b : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let κ : ℕ → ℝ := fun i =>
        if C = ⊤ then 0
        else if b i ≤ C.toReal then 0
        else w C.toReal + (b i - C.toReal) - w (b i)
      (∑ i ∈ Finset.range n, e i * (V (b i) - V (a i))) =
        (∑ i ∈ Finset.range n, e i * (w (b i) - w (a i))) +
        (∑ i ∈ Finset.range n, e i * κ i) := by
  intro ω a b e κ
  have hcell (i : ℕ) (hi : i < n) :
      V (b i) - V (a i) =
        (w (b i) - w (a i)) + κ i := by
    simpa only [a, b, κ] using
      (avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
        X x C hC hxc w V hVtop hVfinite D hD u n ω i hi)
  calc
    (∑ i ∈ Finset.range n, e i * (V (b i) - V (a i)))
        = ∑ i ∈ Finset.range n,
            (e i * (w (b i) - w (a i)) + e i * κ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcell i (Finset.mem_range.mp hi), mul_add]
    _ = (∑ i ∈ Finset.range n, e i * (w (b i) - w (a i))) +
          (∑ i ∈ Finset.range n, e i * κ i) := by
          simp only [Finset.sum_add_distrib]
