-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_true_original_rightdividend_grid_atoms_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:19:04.489851+00:00
-- url     : https://prove2.me/submissions/ce3f6f86-018f-4bd5-9470-92d94d137a7e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false
/-- The actual original right-dividend atoms in any finite strictly
increasing physical time grid are dominated by the D-path increase. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℕ → ℝ≥0)
    (hstrict : ∀ i, s i < s (i + 1)) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      (rightLimit D (s i) ω - D (s i) ω)) ≤
    D (s m) ω - D (s 0) ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hstep := avram_gledger87_original_strict_rightlimit_le_later_dividend
      D hD ω (s m) (s (m + 1)) (hstrict m)
    calc
      (∑ i ∈ Finset.range m, (rightLimit D (s i) ω - D (s i) ω)) +
          (rightLimit D (s m) ω - D (s m) ω) ≤
        (D (s m) ω - D (s 0) ω) +
          (rightLimit D (s m) ω - D (s m) ω) :=
            by
              simpa only [add_comm] using
                (add_le_add_right ih (rightLimit D (s m) ω - D (s m) ω))
      _ ≤ D (s (m + 1)) ω - D (s 0) ω := by linarith
