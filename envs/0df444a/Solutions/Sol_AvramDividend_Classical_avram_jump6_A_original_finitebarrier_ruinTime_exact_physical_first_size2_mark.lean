-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_finitebarrier_ruinTime_exact_physical_first_size2_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:41:20.676116+00:00
-- url     : https://prove2.me/submissions/d4a6f8dc-e217-4ce1-83be-fe90364dd391

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_before_upcrossing
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_nonnegative_pre_mark_reserve_bounds_ruin_time_below
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B J : ℝ≥0 → ℝ) (σ : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t + J t)
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hJzero : ∀ t : ℝ≥0, t < σ → J t = 0)
    (hJneg : ∀ t : ℝ≥0, t ≤ σ → J t ≤ 0)
    (hMark : J σ ≤ -2) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
        (σ : ℝ≥0∞) := by
  have hBound : ∀ s : ℝ≥0, s ≤ σ →
      X.X s ω ≤ (1 / 5 : ℝ) - (1 / 10 : ℝ) := by
    intro s hs
    rw [hPath s]
    have hB := abs_lt.mp (hTube s hs)
    have hJ := hJneg s hs
    norm_num at *
    linarith
  have hDσ : barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω = 0 :=
    barrierStrategy_zero_before_upcrossing
      X (1 / 10 : ℝ) (1 / 5 : ℝ) σ ω hBound
  have hNegative :
      riskProcess X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω < 0 := by
    have hB := abs_lt.mp (hTube σ le_rfl)
    simp only [riskProcess, hDσ, sub_zero, hPath σ]
    norm_num at *
    linarith
  have hPositive :
      ∀ t : ℝ≥0, t < σ →
        0 ≤ riskProcess X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) t ω := by
    intro t ht
    have hDt : barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ) t ω = 0 :=
      barrierStrategy_zero_before_upcrossing X
        (1 / 10 : ℝ) (1 / 5 : ℝ) t ω
        (by intro s hs; exact hBound s (hs.trans (le_of_lt ht)))
    have hB := abs_lt.mp (hTube t (le_of_lt ht))
    simp only [riskProcess, hDt, sub_zero, hPath t, hJzero t ht]
    norm_num at *
    linarith
  have hLower :=
    avram_jump6_A_original_nonnegative_pre_mark_reserve_bounds_ruin_time_below
      X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
      ω σ hPositive
  have hUpper :=
    avram_jump6_A_actual_negative_controlled_reserve_bounds_original_ruin_time
      X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ))
      ω σ hNegative
  exact le_antisymm hUpper hLower
