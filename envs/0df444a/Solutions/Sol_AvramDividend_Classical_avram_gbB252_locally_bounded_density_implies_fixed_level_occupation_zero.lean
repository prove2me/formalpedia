-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB252_locally_bounded_density_implies_fixed_level_occupation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:43:25.656659+00:00
-- url     : https://prove2.me/submissions/229e64e0-82ed-4f5e-bde6-7dc5e61364c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB140_zero_level_from_shrinking_band_occupation
import Theorems.Thm_avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any locally bounded compact spatial occupation density assigns zero time to each level. -/
theorem solution
    (f : ℝ → ℝ) (n : ℕ) (ρ y : ℝ)
    (ℓ : ℝ → ℝ) (R : ℝ)
    (hLocal : ∀ z : ℝ,
      ∃ U ∈ 𝓝 z, Bornology.IsBounded (ℓ '' U))
    (hNonneg : ∀ z, 0 ≤ ℓ z)
    (hSupport : ∀ z, z ∉ Set.Icc (-R) R → ℓ z = 0)
    (hOccupation : ∀ a b : ℝ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        f t ∈ Set.Ioo a b} =
      ∫⁻ z in Set.Ioo a b, ENNReal.ofReal (ℓ z) ∂volume) :
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = y} = 0 := by
  obtain ⟨B, hB0, hB⟩ :=
    avram_gbB242_locally_bounded_compact_localtime_density_controls_interval_occupation
      f n ρ ℓ R hLocal hNonneg hSupport hOccupation
  let S : Set ℝ := {t : ℝ |
    0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = y}
  have hBound (k : ℕ) :
      volume S ≤ ENNReal.ofReal ((2 * B) / ((k : ℝ) + 1)) := by
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hSub : S ⊆
        {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
          f t ∈ Set.Ioo (y - ε) (y + ε)} := by
      intro t ht
      rcases ht with ⟨ht0, htn, htρ, hty⟩
      refine ⟨ht0, htn, htρ, ?_⟩
      change y - ε < f t ∧ f t < y + ε
      rw [hty]
      constructor <;> linarith
    calc
      volume S ≤ volume
        {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
          f t ∈ Set.Ioo (y - ε) (y + ε)} :=
        measure_mono hSub
      _ ≤ ENNReal.ofReal B * volume (Set.Ioo (y - ε) (y + ε)) :=
        hB (y - ε) (y + ε)
      _ = ENNReal.ofReal ((2 * B) / ((k : ℝ) + 1)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hB0]
        congr 1
        dsimp [ε]
        ring
  have hLimit :
      Tendsto (fun k : ℕ =>
        ENNReal.ofReal ((2 * B) / ((k : ℝ) + 1)))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    exact avram_gbB170_ennreal_shrinking_band_rate_tendsto_zero
      (⟨2 * B, by positivity⟩ : ℝ≥0)
  have hZero : volume S = 0 :=
    avram_gbB140_zero_level_from_shrinking_band_occupation
      (volume S) _ hBound hLimit
  exact hZero
