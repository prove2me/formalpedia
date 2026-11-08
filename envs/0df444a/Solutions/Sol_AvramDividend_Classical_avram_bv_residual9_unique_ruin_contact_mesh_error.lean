-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_unique_ruin_contact_mesh_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:35:42.989709+00:00
-- url     : https://prove2.me/submissions/9faa5fa7-d184-48f3-b380-d6931fccae4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_discount_commutator_cell_meshwidth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single ruin-contact negative post-value controls the stopped physical-grid commutator. -/
theorem solution
    (q δ : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (m j : ℕ) (hj : j < m + 1)
    (hmono : ∀ i, i < m + 1 → u i ≤ u (i + 1))
    (hmesh : ∀ i, i < m + 1 →
      (u (i + 1) : ℝ) - (u i : ℝ) ≤ δ)
    (post : ℕ → ℝ)
    (hpost : ∀ i, i < m + 1 → i ≠ j → 0 ≤ post (i + 1)) :
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) ≤
      (q * δ) * max (-post (j + 1)) 0 := by
  have hcontact :
      (∑ i ∈ Finset.range (m + 1),
        max (-post (i + 1)) 0) =
        max (-post (j + 1)) 0 := by
    apply Finset.sum_eq_single j
    · intro i hi hne
      have hp := hpost i (Finset.mem_range.mp hi) hne
      simp [max_eq_right (neg_nonpos.mpr hp)]
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr hj)).elim
  calc
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) ≤
      (∑ i ∈ Finset.range (m + 1),
        (q * δ) * max (-post (i + 1)) 0) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact avram_bv_residual9_discount_commutator_cell_meshwidth
          q (u i : ℝ) (u (i + 1) : ℝ) δ (post (i + 1))
          hq (NNReal.coe_nonneg _)
          (NNReal.coe_le_coe.mpr (hmono i hi')) (hmesh i hi')
    _ = (q * δ) * max (-post (j + 1)) 0 := by
      rw [← Finset.mul_sum, hcontact]
