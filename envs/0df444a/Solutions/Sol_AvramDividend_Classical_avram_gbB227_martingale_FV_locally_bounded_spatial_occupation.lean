-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB227_martingale_FV_locally_bounded_spatial_occupation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:26.91886+00:00
-- url     : https://prove2.me/submissions/d1653883-10f0-452b-90e5-7c83450acd4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
import Theorems.Thm_AvramDividend_Classical_avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Stochastic spatial local time plus local compactness gives original Gaussian uniform occupation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Xsrc : ℝ≥0 → Ω → ℝ) (c σ : ℝ) (hσ : 0 < σ)
    (hM : Martingale (fun t ω =>
      Xsrc t ω - (t : ℝ) * c) 𝓕 P)
    (hQ : Martingale (fun t ω =>
      (Xsrc t ω - (t : ℝ) * c) ^ 2 -
      (t : ℝ) * σ ^ 2) 𝓕 P)
    (hContinuous : ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ≥0 => Xsrc t ω))
    (Dsrc : ℝ≥0 → Ω → ℝ)
    (hFV : ∀ ω, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => Dsrc t ω) Set.univ)
    (x : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0, ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + Xsrc (Real.toNNReal t) ω -
          Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} ≤
      ENNReal.ofReal ((L : ℝ) * (b - a)) := by
  have hRep :=
    avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
      Xsrc c σ hσ hM hQ hContinuous Dsrc hFV x n ρ
  filter_upwards [hRep] with ω hω
  obtain ⟨R, ℓ, hNonneg, hSupport, hLocal, hOccupation⟩ := hω
  have hOcc :=
    avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
      (fun t : ℝ => x + Xsrc (Real.toNNReal t) ω -
        Dsrc (Real.toNNReal t) ω)
      n (ρ ω : ℝ) ℓ R hLocal hNonneg hSupport hOccupation
  obtain ⟨B, hB, hBound⟩ := hOcc
  refine ⟨⟨B, hB⟩, ?_⟩
  intro a b
  calc
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
      x + Xsrc (Real.toNNReal t) ω -
        Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} ≤
      ENNReal.ofReal B * volume (Set.Ioo a b) := hBound a b
    _ = ENNReal.ofReal (B * (b - a)) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_mul hB]
