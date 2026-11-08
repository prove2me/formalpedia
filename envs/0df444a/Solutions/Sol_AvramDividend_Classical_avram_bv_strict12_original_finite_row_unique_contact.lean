-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_original_finite_row_unique_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:55:51.640005+00:00
-- url     : https://prove2.me/submissions/98159308-4b9c-4cb3-b3b0-eb4b9212900f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict12_original_unique_ruin_contact_cell
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The original row-wise monotonicity assumption gives the unique crossing
    property even though the grid is specified only through its last cell. -/
theorem solution
    (n : ℕ) (u : ℕ → ℝ≥0) (τ : ℝ≥0)
    (hmono : ∀ i, i < n + 1 → u i ≤ u (i + 1)) :
    ∀ i j : ℕ, i < n + 1 → j < n + 1 →
      (u i < τ ∧ τ ≤ u (i + 1)) →
      (u j < τ ∧ τ ≤ u (j + 1)) → i = j := by
  let uc : ℕ → ℝ≥0 := fun k => u (min k (n + 1))
  have hcap (k : ℕ) (hk : k ≤ n + 1) : uc k = u k := by
    simp [uc, min_eq_left hk]
  have hstep : ∀ k, uc k ≤ uc (k + 1) := by
    intro k
    by_cases hk : k < n + 1
    · simpa [hcap k (by omega), hcap (k + 1) (by omega)]
        using hmono k hk
    · have hleft : uc k = u (n + 1) := by
        simp [uc, min_eq_right (by omega : n + 1 ≤ k)]
      have hright : uc (k + 1) = u (n + 1) := by
        simp [uc, min_eq_right (by omega : n + 1 ≤ k + 1)]
      rw [hleft, hright]
  have huc : Monotone uc := monotone_nat_of_le_succ hstep
  intro i j hi hj hCrossI hCrossJ
  have hi0 : uc i = u i := hcap i (by omega)
  have hi1 : uc (i + 1) = u (i + 1) := hcap (i + 1) (by omega)
  have hj0 : uc j = u j := hcap j (by omega)
  have hj1 : uc (j + 1) = u (j + 1) := hcap (j + 1) (by omega)
  exact avram_bv_strict12_original_unique_ruin_contact_cell
    uc τ huc i j
      (by simpa [hi0, hi1] using hCrossI)
      (by simpa [hj0, hj1] using hCrossJ)
