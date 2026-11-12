-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54_original_finitecap_gradient_band_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:55:59.071984+00:00
-- url     : https://prove2.me/submissions/5bc8b5d3-451b-4f9e-951b-6d00137cfd87

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_finitecap_compact_first_derivative_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (ρ : Ω → ℝ≥0)
      (Y : Ω → ℝ) (ω : Ω),
      |if t < ρ ω then Real.exp (-(q * (t : ℝ))) *
        (if Y ω ∈ Icc (δ / 2)
          (C.toReal * (((j + 1 : ℕ) : ℝ) /
            ((j + 2 : ℕ) : ℝ))) then deriv w (Y ω) else 1)
      else 0| ≤ B := by
  obtain ⟨M, hM, hband⟩ :=
    avram_gbB56_original_finitecap_compact_first_derivative_bound
      w C hC hFiniteCap hw δ hδ j
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hbound : ∀ y ∈ Icc a b, |deriv w y| ≤ M := by
    simpa only [a, b] using hband
  have hMax1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  have hMaxM : M ≤ max 1 M := le_max_right _ _
  refine ⟨max 1 M, le_trans (by norm_num) hMax1, ?_⟩
  intro t ρ Y ω
  have htn : 0 ≤ (t : ℝ) := NNReal.coe_nonneg _
  have he1 : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    have hn : -(q * (t : ℝ)) ≤ 0 := by nlinarith
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hn)
  by_cases ht : t < ρ ω
  · simp only [if_pos ht]
    by_cases hy : Y ω ∈ Icc a b
    · change |Real.exp (-(q * (t : ℝ))) *
        (if Y ω ∈ Icc a b then deriv w (Y ω) else 1)| ≤ max 1 M
      calc
        _ = Real.exp (-(q * (t : ℝ))) * |deriv w (Y ω)| := by
          simp only [if_pos hy, abs_mul,
            abs_of_nonneg (Real.exp_pos _).le]
        _ ≤ 1 * |deriv w (Y ω)| :=
          mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
        _ = |deriv w (Y ω)| := one_mul _
        _ ≤ M := hbound (Y ω) hy
        _ ≤ max 1 M := hMaxM
    · change |Real.exp (-(q * (t : ℝ))) *
        (if Y ω ∈ Icc a b then deriv w (Y ω) else 1)| ≤ max 1 M
      simpa only [if_neg hy, mul_one,
        abs_of_nonneg (Real.exp_pos _).le] using he1.trans hMax1
  · simp [ht, le_trans (by norm_num : (0 : ℝ) ≤ 1) hMax1]
