-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB250_adapted_gaussian_martingale_FV_spatial_localtime_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:25:22.321768+00:00
-- url     : https://prove2.me/submissions/e7cbca43-04de-4d2d-a0a0-da123976b407
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Generic finite-variation occupation representation specialised to
adapted right-continuous dividend correction. -/
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
      ContinuousWithinAt (fun s : ℝ≥0 => Dsrc s ω)
        (Set.Ici t) t)
    (x : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ R : ℝ, ∃ ℓ : ℝ → ℝ,
      (∀ z, 0 ≤ ℓ z) ∧
      (∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0) ∧
      (∀ z, ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U)) ∧
      (∀ a b : ℝ,
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          x + Xsrc (Real.toNNReal t) ω -
            Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} =
        ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume) := by
  exact avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
    Xsrc c σ hσ hM hQ hContinuous Dsrc hFV x n ρ
