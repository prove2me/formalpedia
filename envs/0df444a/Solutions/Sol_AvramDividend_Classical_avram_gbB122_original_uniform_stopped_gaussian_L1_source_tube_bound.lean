-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB122_original_uniform_stopped_gaussian_L1_source_tube_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:46:41.965526+00:00
-- url     : https://prove2.me/submissions/5345fec9-30a3-4955-bf44-f54bd60bfa16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The exact unit-mesh Gaussian martingale L1 source inherits its tube bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A)
    (n m0 : ℕ) (T : ℝ≥0)
    (hX0 : ∀ ω, X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      M m ω = (Finset.range (m + 1)).sum (fun i =>
        if s i < T then Real.exp (-(q * (s i : ℝ))) *
          (X.X (s (i + 1)) ω - X.X (s i) ω -
            ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
        else 0))
    (hTube : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      ∀ i, s i ≤ T + Δ →
        |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε)
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by
  have hBound (m : ℕ) (hm : m0 ≤ m) (ω : Ω)
      (hω : ω ∈ A) : |M m ω| ≤ ε := by
    rw [hMdef m ω hω]
    exact avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
      X ω n m T (hX0 ω) q ε hq hε (hTube m hm ω hω)
  exact avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
    P A hA N M ε hε m0 hNI hMI hBound hL1
