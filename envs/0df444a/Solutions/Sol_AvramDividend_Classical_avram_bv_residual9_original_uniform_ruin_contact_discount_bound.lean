-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_uniform_ruin_contact_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:45:30.694416+00:00
-- url     : https://prove2.me/submissions/e7af8de6-25d4-431e-8847-7c520084419f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_grid_exact_cell_width
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_unique_ruin_contact_mesh_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual uniform physical-grid discount commutator has order T/(n+2) at one ruin contact. -/
theorem solution
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n j : ℕ) (hj : j < n + 1)
    (post : ℕ → ℝ)
    (hpost : ∀ i, i < n + 1 → i ≠ j → 0 ≤ post (i + 1)) :
    (∑ i ∈ Finset.range (n + 1),
      (Real.exp (-(q * (u n (i + 1) : ℝ))) -
        Real.exp (-(q * (u n i : ℝ)))) * post (i + 1)) ≤
      (q * (T / ((n : ℝ) + 2))) * max (-post (j + 1)) 0 := by
  apply avram_bv_residual9_unique_ruin_contact_mesh_error
    q (T / ((n : ℝ) + 2)) hq (u n) n j hj (hmono n)
    (by
      intro i hi
      exact le_of_eq
        (avram_a19_uniform_grid_exact_cell_width T hT u huniform n i))
    post hpost
