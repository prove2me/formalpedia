-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_strict_stopped_prefix_rightdividend_atoms_le_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:26:32.739938+00:00
-- url     : https://prove2.me/submissions/98da2375-48e9-4faa-95f1-25672f152c5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_true_original_rightdividend_grid_atoms_telescope
import Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false
/-- Every genuine pre-stop rightdividend mesh prefix mass is controlled
by the actual cumulative D at the original stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℕ → ℝ≥0)
    (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (ρ : ℝ≥0) (hbefore : s m < ρ) :
    (∑ i ∈ Finset.range m,
      (rightLimit D (s i) ω - D (s i) ω)) ≤
      D ρ ω - D (s 0) ω := by
  have hsum :=
    avram_agentB_true_original_rightdividend_grid_atoms_telescope
      D hD ω s hstrict m
  have hclose := avram_gledger87_original_strict_rightlimit_le_later_dividend
    D hD ω (s m) ρ hbefore
  have hcurrent := dividendStrategy_le_rightLimit D hD ω (s m)
  linarith
