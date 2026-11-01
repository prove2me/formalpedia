-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:25:25.604735+00:00
-- url     : https://prove2.me/submissions/5805a367-21ae-4513-88ce-a4c773359440

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 μ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Adapted 𝓕 B)
    (hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) ∂μ) =
      (∫ ω, B (u 0) ω * M (u 0) ω ∂μ) -
      (∫ ω, B (u n) ω * M (u n) ω ∂μ) := by
  have hBsm (r : ℝ≥0) : AEStronglyMeasurable (B r) μ :=
    ((hB r).mono (𝓕.le r) le_rfl).aestronglyMeasurable
  have hBnorm (r : ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖B r ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hBbound r ω).1]
    exact (hBbound r ω).2
  have hIntProd (r v : ℝ≥0) :
      Integrable (fun ω => B r ω * M v ω) μ :=
    (hM.integrable v).bdd_mul (hBsm r) (hBnorm r)
  have hTermInt (i : ℕ) :
      Integrable (fun ω =>
        M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) μ := by
    have h := (hIntProd (u i) (u (i + 1))).sub
      (hIntProd (u (i + 1)) (u (i + 1)))
    have heq : (fun ω =>
        M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) =
        (fun ω => B (u i) ω * M (u (i + 1)) ω -
          B (u (i + 1)) ω * M (u (i + 1)) ω) := by
      funext ω
      ring
    rw [heq]
    exact h
  let F : ℕ → ℝ := fun i => ∫ ω, B (u i) ω * M (u i) ω ∂μ
  have hStep (i : ℕ) :
      (∫ ω, M (u (i + 1)) ω *
        (B (u i) ω - B (u (i + 1)) ω) ∂μ) =
        F i - F (i + 1) :=
    avram_wave4_03_martingale_oneStep_consumption_exact_expectation_balance
      M hM B hB hBbound (u i) (u (i + 1)) (hu (Nat.le_succ i))
  have hTel (k : ℕ) :
      (∑ i ∈ Finset.range k, (F i - F (i + 1))) = F 0 - F k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∫ ω, ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) ∂μ) =
        ∑ i ∈ Finset.range n,
          (∫ ω, M (u (i + 1)) ω *
            (B (u i) ω - B (u (i + 1)) ω) ∂μ) := by
      exact integral_finset_sum (Finset.range n) (by
        intro i hi
        exact hTermInt i)
    _ = ∑ i ∈ Finset.range n, (F i - F (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hStep i
    _ = F 0 - F n := hTel n
    _ = (∫ ω, B (u 0) ω * M (u 0) ω ∂μ) -
          (∫ ω, B (u n) ω * M (u n) ω ∂μ) := rfl
