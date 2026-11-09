-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_residual_bounded_horizon_uniform_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T09:58:51.792947+00:00
-- url     : https://prove2.me/submissions/84746729-97f9-4b6a-ba82-917298ae65bd

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform L² Cauchy control over bounded physical stopping horizons.
The physical isometry remains a distinct, explicitly required source hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (H : ℝ≥0)
    (R : ℕ → ℝ≥0 → Ω → ℝ)
    (hR : ∀ (n : ℕ) (T : ℝ≥0) (ω : Ω),
      R n T ω = avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
    (hIso : ∀ (n m : ℕ) (T : ℝ≥0), T ≤ H →
      Integrable (fun ω => (R n T ω - R m T ω) ^ 2) P ∧
      (∫ ω, (R n T ω - R m T ω) ^ 2 ∂P) ≤
        (H : ℝ) *
          (∫ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            z ^ 2 ∂X.ν)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ m : ℕ, N ≤ m →
          ∀ T : ℝ≥0, T ≤ H →
            Integrable (fun ω => (R n T ω - R m T ω) ^ 2) P ∧
            (∫ ω, (R n T ω - R m T ω) ^ 2 ∂P) < ε := by
  intro ε hε
  have hden : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have heps : 0 < ε / ((H : ℝ) + 1) := div_pos hε hden
  obtain ⟨N, hN⟩ :=
    avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail X _ heps
  refine ⟨N, ?_⟩
  intro n hn m hm T hT
  obtain ⟨hI, hBound⟩ := hIso n m T hT
  have hMin : N ≤ min n m := le_min hn hm
  obtain ⟨hStripInt, hStrip⟩ := hN (min n m) hMin (max n m)
  refine ⟨hI, ?_⟩
  have hNonneg : 0 ≤
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) :=
    integral_nonneg (fun z => sq_nonneg z)
  have hStep : (H : ℝ) *
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) ≤
      ((H : ℝ) + 1) *
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) := by
    have hHle : (H : ℝ) ≤ (H : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hHle hNonneg
  have hStrict : ((H : ℝ) + 1) *
      (∫ z in Ioc
        (-(1 / (((min n m : ℕ) : ℝ) + 1)))
        (-(1 / (((max n m : ℕ) : ℝ) + 1))),
        z ^ 2 ∂X.ν) <
      ((H : ℝ) + 1) * (ε / ((H : ℝ) + 1)) :=
    mul_lt_mul_of_pos_left hStrip hden
  have hCancel : ((H : ℝ) + 1) * (ε / ((H : ℝ) + 1)) = ε := by
    field_simp
  exact lt_of_le_of_lt (le_trans hBound hStep)
    (by simpa only [hCancel] using hStrict)
