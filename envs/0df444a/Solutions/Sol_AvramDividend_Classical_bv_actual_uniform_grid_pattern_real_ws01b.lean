-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_uniform_grid_pattern_real_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:14:58.4299+00:00
-- url     : https://prove2.me/submissions/123614ca-3e93-48c1-89a5-d407ca5cc012

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_residual_active_pattern_product_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For the actual finite-activity Lévy process, every fixed-length
grid pattern has the exact joint Bernoulli probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (active : Finset ℕ)
    (h : ℝ)
    (hgap : ∀ i : ℕ, i < n →
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) = h) :
    P.real {ω : Ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ active then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
    ∏ i ∈ Finset.range n,
      if i ∈ active then
        1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))
      else
        Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hProduct :=
    bv_actual_grid_residual_active_pattern_product_ws01b X t ht n active
  rw [Measure.real_def, hProduct, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hsti : t i ≤ t (i + 1) := ht (Nat.le_succ i)
  have hPositive :=
    bv_actual_residual_increment_positive_probability X hBV hFinite
      (t i) (t (i + 1)) hsti
  have hZero :=
    bv_actual_residual_increment_zero_probability X hBV hFinite
      (t i) (t (i + 1)) hsti
  have hD (ω : Ω) :
      ((t (i + 1) : ℝ) * X.drift - X.X (t (i + 1)) ω) -
        ((t i : ℝ) * X.drift - X.X (t i) ω) =
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) * X.drift -
        (X.X (t (i + 1)) ω - X.X (t i) ω) := by
    rw [NNReal.coe_sub hsti]
    ring
  by_cases hiAct : i ∈ active
  · simp only [if_pos hiAct, Set.mem_Iio]
    have heq : {ω : Ω |
      X.X (t (i + 1)) ω - X.X (t i) ω <
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))} =
      {ω : Ω | 0 <
        ((t (i + 1) : ℝ) * X.drift - X.X (t (i + 1)) ω) -
          ((t i : ℝ) * X.drift - X.X (t i) ω)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hD ω]
      constructor <;> intro hh <;> linarith
    rw [← Measure.real_def, heq, hPositive, hgap i (Finset.mem_range.mp hi)]
  · simp only [if_neg hiAct, Set.mem_singleton_iff]
    have heq : {ω : Ω |
      X.X (t (i + 1)) ω - X.X (t i) ω =
      X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))} =
      {ω : Ω |
        ((t (i + 1) : ℝ) * X.drift - X.X (t (i + 1)) ω) -
          ((t i : ℝ) * X.drift - X.X (t i) ω) = 0} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hD ω]
      constructor <;> intro hh <;> linarith
    rw [← Measure.real_def, heq, hZero, hgap i (Finset.mem_range.mp hi)]
