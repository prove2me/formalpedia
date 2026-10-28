-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_aligned_dyadic_active_count_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:59:57.264453+00:00
-- url     : https://prove2.me/submissions/cba2341a-164e-42de-9018-280838198e88

import Theorems.Thm_AvramDividend_Classical_bv_aligned_grid_active_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_bv_actual_uniform_grid_active_expected_le_intensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal

/-- The actual finite-activity Levy residual has a finite number of active dyadic cells on every refinement a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℕ → ℝ≥0) (T : ℝ)
    (hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i)
    (hStep : ∀ n i : ℕ, i < 2 ^ n →
      grid n i ≤ grid n (i + 1))
    (hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        T / ((2 ^ n : ℕ) : ℝ))) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ,
      (∑ i ∈ range (2 ^ n),
        ite (((grid n i : ℝ) * X.drift - X.X (grid n i) ω) <
          ((grid n (i + 1) : ℝ) * X.drift - X.X (grid n (i + 1)) ω))
          (1 : ℕ) 0) ≤ K := by
  let Y : Ω → ℝ≥0 → ℝ := fun ω t =>
    (t : ℝ) * X.drift - X.X t ω
  have hY (t : ℝ≥0) : Measurable (fun ω => Y ω t) :=
    measurable_const.sub (X.adapted.measurable)
  let C : ℝ≥0∞ := ENNReal.ofReal ((X.ν (Iio (0 : ℝ))).toReal * T)
  have hBound (n : ℕ) :
      (∫⁻ ω, (∑ i ∈ range (2 ^ n),
        ite (Y ω (grid n i) < Y ω (grid n (i + 1)))
          (1 : ℕ) 0 : ℕ) ∂P) ≤ C := by
    have h := bv_actual_uniform_grid_active_expected_le_intensity
      X hBV hFinite (grid n) (2 ^ n)
      (pow_pos (by decide) n) T (hStep n) (hMesh n)
    have hEq :
        (∫⁻ ω, (∑ i ∈ range (2 ^ n),
          ite (Y ω (grid n i) < Y ω (grid n (i + 1)))
            (1 : ℕ) 0 : ℕ) ∂P) =
        (∫⁻ ω, ∑ i ∈ range (2 ^ n),
          ({ω : Ω | 0 <
            ((grid n (i + 1) : ℝ) * X.drift - X.X (grid n (i + 1)) ω) -
            ((grid n i : ℝ) * X.drift - X.X (grid n i) ω)}).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂P) := by
      apply lintegral_congr
      intro ω
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      have hiff :
          (Y ω (grid n i) < Y ω (grid n (i + 1))) ↔
          (0 < ((grid n (i + 1) : ℝ) * X.drift -
            X.X (grid n (i + 1)) ω) -
            ((grid n i : ℝ) * X.drift - X.X (grid n i) ω)) := by
        dsimp [Y]
        constructor <;> intro hh <;> linarith
      by_cases hp : Y ω (grid n i) < Y ω (grid n (i + 1))
      · have hq := hiff.mp hp
        simp [hp, hq]
      · have hq : ¬ (0 < ((grid n (i + 1) : ℝ) * X.drift -
            X.X (grid n (i + 1)) ω) -
            ((grid n i : ℝ) * X.drift - X.X (grid n i) ω)) := by
          intro h
          exact hp (hiff.mpr h)
        simp [hp, hq]
    rw [hEq]
    exact h
  exact bv_aligned_grid_active_count_ae_finite P Y grid C hAlign hY
    hBound ENNReal.ofReal_lt_top
