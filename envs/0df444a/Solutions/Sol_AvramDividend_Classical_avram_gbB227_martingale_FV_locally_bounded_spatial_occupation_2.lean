-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB227_martingale_FV_locally_bounded_spatial_occupation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:31:32.324942+00:00
-- url     : https://prove2.me/submissions/3d803b91-6646-4875-856c-5ae710a286f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_gbB233_martingale_FV_bounded_localtime_occupation_density
import Theorems.Thm_AvramDividend_Classical_avram_gbB234_finite_ENNReal_scaled_interval_volume_ofReal
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

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
  have hDensity :=
    AvramDividend.Classical.avram_gbB233_martingale_FV_bounded_localtime_occupation_density
      Xsrc c σ hσ hM hQ hContinuous Dsrc hFV x n ρ
  filter_upwards [hDensity] with ω hω
  obtain ⟨ℓ, B, hB, hℓ, hOccupation⟩ := hω
  refine ⟨⟨B.toReal, ENNReal.toReal_nonneg⟩, ?_⟩
  intro a b
  have hBound :
      (∫⁻ z in Set.Ioo a b, ℓ z ∂volume) ≤
        B * volume (Set.Ioo a b) := by
    calc
      (∫⁻ z in Set.Ioo a b, ℓ z ∂volume) ≤
          ∫⁻ z in Set.Ioo a b, B ∂volume :=
        lintegral_mono (fun z => hℓ z)
      _ = B * volume (Set.Ioo a b) := by
        simp [lintegral_const, mul_comm]
  calc
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
      x + Xsrc (Real.toNNReal t) ω -
        Dsrc (Real.toNNReal t) ω ∈ Set.Ioo a b} =
        ∫⁻ z in Set.Ioo a b, ℓ z ∂volume :=
      hOccupation a b
    _ ≤ B * volume (Set.Ioo a b) := hBound
    _ = ENNReal.ofReal (B.toReal * (b - a)) :=
      AvramDividend.Classical.avram_gbB234_finite_ENNReal_scaled_interval_volume_ofReal B hB a b
    _ = ENNReal.ofReal (((⟨B.toReal, ENNReal.toReal_nonneg⟩ : ℝ≥0) : ℝ) *
        (b - a)) := rfl
