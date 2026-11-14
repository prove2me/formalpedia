-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB251_adapted_gaussian_martingale_FV_fixed_level_null_occupation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:32.303779+00:00
-- url     : https://prove2.me/submissions/68579d6d-c3ec-4684-abd4-10c23a9754b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB250_adapted_gaussian_martingale_FV_spatial_localtime_representation
import Theorems.Thm_AvramDividend_Classical_avram_gbB252_locally_bounded_density_implies_fixed_level_occupation_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Adapted semimartingale local time implies source-preserving zero fixed-level occupation. -/
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
    (hDAdapt : Adapted 𝓕 Dsrc)
    (hDright : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s : ℝ≥0 => Dsrc s ω) (Set.Ici t) t)
    (x b : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + Xsrc (Real.toNNReal t) ω -
          Dsrc (Real.toNNReal t) ω = b} = 0 := by
  have hRep :=
    avram_gbB250_adapted_gaussian_martingale_FV_spatial_localtime_representation
      Xsrc c σ hσ hM hQ hContinuous Dsrc hFV hDAdapt hDright x n ρ
  filter_upwards [hRep] with ω hω
  obtain ⟨R, ℓ, hNonneg, hSupport, hLocal, hOccupation⟩ := hω
  exact
    avram_gbB252_locally_bounded_density_implies_fixed_level_occupation_zero
      (fun t : ℝ => x + Xsrc (Real.toNNReal t) ω -
        Dsrc (Real.toNNReal t) ω)
      n (ρ ω : ℝ) b ℓ R hLocal hNonneg hSupport hOccupation
