-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger111_monotone_grid_Ioc_cash_le_strict_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:53:12.710726+00:00
-- url     : https://prove2.me/submissions/c1a5c110-a58c-414d-98cb-ef097689a3b0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger88_monotone_grid_Ioc_cash_exact_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Complete original interior grid cells charge pre-stop cash at most once. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ) :
    (∑ i ∈ Finset.range k,
      ∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ) ≤
    ∫⁻ s in Ioo 0 ρ, f s ∂μ := by
  rw [avram_gledger88_monotone_grid_Ioc_cash_exact_partition μ f v hv k]
  apply lintegral_mono_set
  intro t ht
  have ht0 : 0 < t := by simpa [hv0] using ht.1
  exact ⟨ht0, lt_of_le_of_lt ht.2 hvk⟩
