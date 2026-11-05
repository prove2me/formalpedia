-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_physical_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:34:10.147757+00:00
-- url     : https://prove2.me/submissions/c38457cd-c829-4cb9-8351-c5fc0b7ccfc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
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
    (u : ℕ → ℝ≥0) (n : ℕ)
    (q : ℝ) (hq : 0 ≤ q)
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hTaylor : ∀ ω i, i < n → C ≠ ⊤ →
      C.toReal < x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
      |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w C.toReal -
        deriv w C.toReal *
          (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal)| ≤
      ε * |x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal|) :
    ∀ ω,
      (∀ i, i < n → C ≠ ⊤ →
        x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) →
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let b : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      let d : ℕ → ℝ := fun i =>
        X.X (u (i + 1)) ω - X.X (u i) ω
      let κ : ℕ → ℝ := fun i =>
        if C = ⊤ then 0
        else if b i ≤ C.toReal then 0
        else w C.toReal + (b i - C.toReal) - w (b i)
      |∑ i ∈ Finset.range n, e i * κ i| ≤
        ε * ∑ i ∈ Finset.range n, e i * |d i| := by
  classical
  intro ω hStartCap e b d κ
  have hcell : ∀ i, i < n →
      |κ i| ≤ ε * |d i| := by
    intro i hi
    have h :=
      avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
        X x C hC hxc w V hVtop hVfinite D hD u n
        hSlope ε hε ω i hi (hTaylor ω i hi)
    have hCap :=
      avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
        X x C hC hxc w V hVtop hVfinite D hD u n ω i hi
    change
      V (b i) - V (x + X.X (u i) ω - rightLimit D (u i) ω) =
        (w (b i) - w (x + X.X (u i) ω - rightLimit D (u i) ω)) +
        κ i at hCap
    rw [hCap] at h
    have hBase : |κ i| ≤ ε * |b i - C.toReal| := by
      convert h using 1
      congr 1 <;> ring
    by_cases ht : C = ⊤
    · simp only [κ, if_pos ht, abs_zero]
      exact mul_nonneg hε (abs_nonneg _)
    · by_cases hb : b i ≤ C.toReal
      · simp only [κ, if_neg ht, if_pos hb, abs_zero]
        exact mul_nonneg hε (abs_nonneg _)
      · have hpre := hStartCap i hi ht
        have hbd : b i - C.toReal ≤ d i := by
          dsimp only [b, d]
          linarith
        have hd : 0 ≤ d i :=
          le_trans (le_of_lt (sub_pos.mpr (lt_of_not_ge hb))) hbd
        have hover : |b i - C.toReal| ≤ |d i| := by
          rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hb)), abs_of_nonneg hd]
          exact hbd
        exact hBase.trans (mul_le_mul_of_nonneg_left hover hε)
  have he : ∀ i, 0 ≤ e i := by
    intro i
    exact (Real.exp_pos _).le
  calc
    |∑ i ∈ Finset.range n, e i * κ i| ≤
        ∑ i ∈ Finset.range n, |e i * κ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, e i * |κ i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (he i)]
    _ ≤ ∑ i ∈ Finset.range n, e i * (ε * |d i|) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcell i (Finset.mem_range.mp hi)) (he i)
    _ = ε * ∑ i ∈ Finset.range n, e i * |d i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
