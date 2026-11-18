-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB113_original_stopped_grid_L1_limit_bounded_on_overshoot_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:30:53.525485+00:00
-- url     : https://prove2.me/submissions/d4d09e66-376f-458f-94a2-59332da8fcff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The source L1 limit inherits the stopped physical-grid tube noise bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A) (m0 : ℕ) (T : ℝ≥0)
    (s : ℕ → ℕ → ℝ≥0) (Δ : ℕ → ℝ≥0)
    (hs : ∀ m, Monotone (s m))
    (hs0 : ∀ m, s m 0 = 0)
    (hstep : ∀ m i, s m (i + 1) = s m i + Δ m)
    (hX0 : ∀ ω, X.X 0 ω = 0) (q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A → M m ω =
      (Finset.range (m + 1)).sum (fun i =>
        if s m i < T then Real.exp (-(q * (s m i : ℝ))) *
          (X.X (s m (i + 1)) ω - X.X (s m i) ω -
            ((s m (i + 1) : ℝ) - (s m i : ℝ)) * X.c)
        else 0))
    (hTube : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A →
      ∀ i, s m i ≤ T + Δ m →
        |X.X (s m i) ω - (s m i : ℝ) * X.c| ≤ ε)
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by
  have hBound (m : ℕ) (hm : m0 ≤ m) (ω : Ω)
      (hω : ω ∈ A) : |M m ω| ≤ ε := by
    rw [hMdef m ω hω]
    exact avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
      X ω m (s m) (hs m) (hs0 m) (Δ m) T (hstep m)
      (hX0 ω) q ε hq hε (hTube m hm ω hω)
  exact avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
    P A hA N M ε hε m0 hNI hMI hBound hL1
