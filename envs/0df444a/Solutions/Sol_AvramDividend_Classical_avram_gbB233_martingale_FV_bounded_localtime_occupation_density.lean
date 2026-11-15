-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB233_martingale_FV_bounded_localtime_occupation_density
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:44:14.946442+00:00
-- url     : https://prove2.me/submissions/34da780a-3358-4dfd-8350-cf4f73cf2d7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
import Theorems.Thm_AvramDividend_Classical_avram_gbB241_locally_bounded_compact_support_density_uniform
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
open AvramDividend.Classical

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
    ∀ᵐ ω ∂P, ∃ (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0∞),
      B ≠ ⊤ ∧
      (∀ z : ℝ, ℓ z ≤ B) ∧
      (∀ a b : ℝ,
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          x + Xsrc (Real.toNNReal t) ω -
            Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} =
        ∫⁻ z in Set.Ioo a b, ℓ z ∂volume) := by
  have hSource :=
    avram_gbB243_gaussian_martingale_FV_spatial_localtime_representation
      Xsrc c σ hσ hM hQ hContinuous Dsrc hFV x n ρ
  filter_upwards [hSource] with ω hω
  obtain ⟨R, ℓ, hNonneg, hSupport, hLocal, hOcc⟩ := hω
  obtain ⟨B, hB0, hBnd⟩ :=
    avram_gbB241_locally_bounded_compact_support_density_uniform
      ℓ R hLocal hNonneg hSupport
  refine ⟨(fun z => ENNReal.ofReal (ℓ z)), ENNReal.ofReal B,
    by simp, ?_, ?_⟩
  · intro z
    exact ENNReal.ofReal_le_ofReal (hBnd z)
  · exact hOcc
