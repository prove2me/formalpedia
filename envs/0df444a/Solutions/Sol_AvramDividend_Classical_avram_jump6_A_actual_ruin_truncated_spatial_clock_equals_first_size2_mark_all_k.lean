-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_ruin_truncated_spatial_clock_equals_first_size2_mark_all_k
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:49:51.495829+00:00
-- url     : https://prove2.me/submissions/aefa8fc6-056c-4904-b9cc-076eb986ac60

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
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
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ : ℝ≥0) (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (hSmall : (σ : ℝ) ≤ 1 / 500)
    (hρ : ρ ω =
      (min (ruinTime X (1 / 10 : ℝ)
        (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)
        (1 : ℝ≥0∞)).toNNReal)
    (hκ : ∀ k, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) :
    ∀ k : ℕ, κ k ω = σ := by
  have hRuin :=
    avram_jump6_A_original_finite_barrier_first_size2_mark_ruin_time_exact
      X ω B N σ hPath hTube hBefore hMark
  have hσle : (σ : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by
    have hσ0 : (σ : ℝ) ≤ (1 : ℝ) := by linarith
    exact_mod_cast hσ0
  have hρeq : ρ ω = σ := by
    rw [hρ, hRuin, min_eq_left hσle]
    simp
  have hNoUp :=
    (avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
      X ω B N σ hPath hTube hMark).1
  intro k
  have hBelow : ∀ t : ℝ≥0, t ≤ σ →
      X.X t ω ≤ (k : ℝ) + 1 := by
    intro t ht
    have hs := hNoUp t ht
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hClip :=
    avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
      X ω σ ((k : ℝ) + 1) hBelow
  rw [hκ k, hρeq]
  exact hClip
