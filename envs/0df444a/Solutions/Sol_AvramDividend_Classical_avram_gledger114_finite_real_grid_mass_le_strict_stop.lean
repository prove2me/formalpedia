-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger114_finite_real_grid_mass_le_strict_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:14:31.758304+00:00
-- url     : https://prove2.me/submissions/5fe6307c-8577-47e4-a5e8-12445d5d2973

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A finite original strict-stop dividend measure bounds the real masses of its grid cells. -/
theorem solution
    (μ : Measure ℝ) (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hfinite : μ (Ioo (0 : ℝ) ρ) ≠ ⊤) :
    (∑ i ∈ Finset.range k, (μ (Ioc (v i) (v (i + 1)))).toReal) ≤
      (μ (Ioo (0 : ℝ) ρ)).toReal := by
  have hsum :
      (∑ i ∈ Finset.range k, μ (Ioc (v i) (v (i + 1)))) ≤
      μ (Ioo (0 : ℝ) ρ) := by
    simpa using avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop
      μ (fun _ => 1) v hv hv0 k ρ hvk
  have hsumfin :
      (∑ i ∈ Finset.range k, μ (Ioc (v i) (v (i + 1)))) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hsum
  have hcells : ∀ i ∈ Finset.range k,
      μ (Ioc (v i) (v (i + 1))) ≠ ⊤ := by
    intro i hi
    exact ne_of_lt (ENNReal.lt_top_of_sum_ne_top hsumfin hi)
  calc
    (∑ i ∈ Finset.range k,
        (μ (Ioc (v i) (v (i + 1)))).toReal) =
        (∑ i ∈ Finset.range k, μ (Ioc (v i) (v (i + 1)))).toReal := by
          exact (ENNReal.toReal_sum hcells).symm
    _ ≤ (μ (Ioo (0 : ℝ) ρ)).toReal :=
      ENNReal.toReal_mono hfinite hsum
