-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB60_finitecap_clipped_gradient_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:03:38.574013+00:00
-- url     : https://prove2.me/submissions/47b4fc37-0f91-4817-86ac-9c3a2d876ad6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_finitecap_compact_first_derivative_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Discounted stopped clipped gradients admit a compact-band bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (ρ : Ω → ℝ≥0)
      (Y : Ω → ℝ) (ω : Ω),
      |if t < ρ ω then
        Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc (δ / 2)
            (C.toReal * (((j + 1 : ℕ) : ℝ) /
              ((j + 2 : ℕ) : ℝ))) then
              deriv w (Y ω) else 1)
      else 0| ≤ B := by
  obtain ⟨B, hB, hderiv⟩ :=
    avram_gbB56_original_finitecap_compact_first_derivative_bound
      w C hC hFiniteCap hw δ hδ j
  refine ⟨max B 1, le_trans hB (le_max_left _ _), ?_⟩
  intro t ρ Y ω
  by_cases ht : t < ρ ω
  · simp only [if_pos ht]
    have hqtime : 0 ≤ q * (t : ℝ) :=
      mul_nonneg (le_of_lt hq) (NNReal.coe_nonneg t)
    have he : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqtime)
    have hep : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
      le_of_lt (Real.exp_pos _)
    have hclip :
        |if Y ω ∈ Icc (δ / 2)
          (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
          then deriv w (Y ω) else 1| ≤ max B 1 := by
      split_ifs with hmem
      · exact (hderiv (Y ω) hmem).trans (le_max_left _ _)
      · simpa using (le_max_right B 1)
    rw [abs_mul, abs_of_nonneg hep]
    calc
      Real.exp (-(q * (t : ℝ))) * _ ≤ 1 * _ :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ 1 * max B 1 := mul_le_mul_of_nonneg_left hclip (by norm_num)
      _ = max B 1 := one_mul _
  · simp only [if_neg ht, abs_zero]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right B 1)
