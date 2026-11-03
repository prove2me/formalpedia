-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:22:23.553223+00:00
-- url     : https://prove2.me/submissions/301eca70-542a-4af4-ad07-9029e8bfb477

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- Every original left-continuous dividend path has a uniform total
    right-payment bound on all grids clipped at one fixed stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hzero : ∀ n, u n 0 = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (min (u n (k n)) (τ ω)) ω -
        rightLimit D (min (u n 0) (τ ω)) ω ≤ B := by
  have hmono : Monotone (fun t : ℝ≥0 => rightLimit D t ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  refine ⟨rightLimit D (τ ω) ω - rightLimit D 0 ω, ?_, ?_⟩
  · exact sub_nonneg.mpr (hmono (by positivity))
  · intro n
    have hStart : min (u n 0) (τ ω) = 0 := by
      simp [hzero n]
    rw [hStart]
    exact sub_le_sub_right (hmono (min_le_right _ _)) _

