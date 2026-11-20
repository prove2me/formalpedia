-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_all_spatial_kappa_equal_first_negative_mark_on_real_BrownianPoisson_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:47:31.714919+00:00
-- url     : https://prove2.me/submissions/0b425741-93cd-41dd-9dbb-a38cdef1d10d

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
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
    (hMark : 1 ≤ N σ)
    (hρ : ρ ω = σ)
    (hκ : ∀ k, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) :
    ∀ k : ℕ, κ k ω = σ := by
  have hSmall := (avram_jump6_A_actual_Brownian_negative_mark_tube_forces_ruin_without_upper_cap_exit
    X ω B N σ hPath hTube hMark).1
  intro k
  have hBelow : ∀ t : ℝ≥0, t ≤ σ →
      X.X t ω ≤ (k : ℝ) + 1 := by
    intro t ht
    have hB := hSmall t ht
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have hExact :=
    avram_jump6_A_original_spatial_exit_clip_identity_when_physical_path_below_upbarrier
      X ω σ ((k : ℝ) + 1) hBelow
  rw [hκ k, hρ]
  exact hExact
