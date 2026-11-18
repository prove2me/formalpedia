-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:26:53.005202+00:00
-- url     : https://prove2.me/submissions/076bb59d-0c8f-4160-b210-ef72590d53f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- The original upper-strip G/H source is exactly the stopped linear noise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (ρ : Ω → ℝ≥0)
    (hρ : ρ ω =
      sInf ((Icc (0 : ℝ≥0) T ∩
        (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
          Ici (-(5 / 44 : ℝ))) ∪ {T}))
    (m : ℕ) (s : ℕ → ℝ≥0) (Z v : ℕ → ℝ)
    (q a : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i =>
      (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
    (Finset.range (m + 1)).sum (fun i =>
      (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
      else 0) * Z i +
      (if s i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then iteratedDeriv 2 w (Y i) else 0)
      else 0) * (Z i ^ 2 - v i)) =
    (Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) * Z i else 0)
    := by
  have hStop : ρ ω = T := by
    rw [hρ]
    exact avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube X T ω hTube
  rw [hStop]
  exact avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
    X T ω hTube m s Z v q a w
