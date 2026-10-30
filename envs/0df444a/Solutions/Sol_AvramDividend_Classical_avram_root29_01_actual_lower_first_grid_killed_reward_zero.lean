-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_lower_first_grid_killed_reward_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:03:58.505656+00:00
-- url     : https://prove2.me/submissions/483dc11d-3062-4303-ac96-3b4c366c01ab

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Genuine original-Levy first-exit sampled reward vanishes on the terminal
zero-scale lower branch, including continuous lower-history killing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) (hWnonneg : ∀ z, 0 ≤ W z)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτT : τ < T) (hEndZero : W (x + X.X τ ω) = 0)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ (K n η : ℝ≥0) * mesh n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (((K n η : ℝ≥0) * mesh n) : ℝ))) *
          W (x + X.X ((K n η : ℝ≥0) * mesh n) η)) ω)
      atTop (nhds 0) := by
  have hRaw := chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
    X q W hW hzero ω lower upper x τ T
    hτ hτT mesh hmesh hpos m hcap K hK
  have hEnd :
      Real.exp (-(q * (τ : ℝ))) * W (x + X.X τ ω) = 0 := by
    rw [hEndZero, mul_zero]
  rw [hEnd] at hRaw
  have hN (n : ℕ) :
      0 ≤ W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω) :=
    hWnonneg _
  exact avram_root29_01_actual_lower_killed_reward_zero_of_raw_zero
    X q W x ω (fun n => (K n ω : ℝ≥0) * mesh n) hN hRaw
