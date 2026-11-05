-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:39:17.313373+00:00
-- url     : https://prove2.me/submissions/2fa36275-9805-4661-bfff-9819d993c3ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Uniform weighted physical pure drift Taylor error against exact total grid drift variation. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (u : ℕ → ℝ≥0) (n : ℕ) (z c : ℕ → ℝ),
        (∀ i, i < n → Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
          ε * (∑ i ∈ Finset.range n, |c i|) := by
  intro ε hε
  obtain ⟨δ, hδ, hCell⟩ :=
    avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell
      w C hwC1 hOpen a b hBand ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u n z c hBandCells hSmall
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |Real.exp (-(q * (u i : ℝ))) *
          (w (z i + c i) - w (z i) - deriv w (z i) * c i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      have hNonpos : -(q * (u i : ℝ)) ≤ 0 := by
        exact neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg _))
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-(q * (u i : ℝ))) *
          |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
            1 * |w (z i + c i) - w (z i) - deriv w (z i) * c i| :=
          mul_le_mul_of_nonneg_right
            (Real.exp_le_one_iff.mpr hNonpos) (abs_nonneg _)
        _ = |w (z i + c i) - w (z i) - deriv w (z i) * c i| :=
          one_mul _
        _ ≤ ε * |c i| :=
          hCell (z i) (c i) (hBandCells i (Finset.mem_range.mp hi))
            (hSmall i (Finset.mem_range.mp hi))
    _ = ε * (∑ i ∈ Finset.range n, |c i|) := by
      rw [Finset.mul_sum]
