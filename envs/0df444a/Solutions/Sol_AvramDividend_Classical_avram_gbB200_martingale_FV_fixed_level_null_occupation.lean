-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB200_martingale_FV_fixed_level_null_occupation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:31:11.517206+00:00
-- url     : https://prove2.me/submissions/b5fbb7f5-8b13-4f72-abb4-fdcdc8948bd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB208_martingale_FV_uniform_band_occupation_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB140_zero_level_from_shrinking_band_occupation
import Theorems.Thm_avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every fixed-level occupation mass is squeezed by a uniform shrinking band rate. -/
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
    (x b : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        x + Xsrc (Real.toNNReal t) ω -
          Dsrc (Real.toNNReal t) ω = b} = 0 := by
  have hRate :=
    avram_gbB208_martingale_FV_uniform_band_occupation_bound
      Xsrc c σ hσ hM hQ hContinuous Dsrc hFV x b n ρ
  filter_upwards [hRate] with ω hω
  obtain ⟨L, hL⟩ := hω
  let E : Set ℝ := {t : ℝ |
    0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
    x + Xsrc (Real.toNNReal t) ω -
      Dsrc (Real.toNNReal t) ω = b}
  have hBound (k : ℕ) : volume E ≤
      ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)) := by
    calc
      volume E ≤ volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + Xsrc (Real.toNNReal t) ω -
            Dsrc (Real.toNNReal t) ω - b) <
            (1 : ℝ) / ((k : ℝ) + 1)} := by
            apply measure_mono
            intro t ht
            refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
            rw [ht.2.2.2]
            norm_num
            positivity
      _ ≤ ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)) := hL k
  exact avram_gbB140_zero_level_from_shrinking_band_occupation
    (volume E)
    (fun k : ℕ => ENNReal.ofReal ((L : ℝ) / ((k : ℝ) + 1)))
    hBound (avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero L)

