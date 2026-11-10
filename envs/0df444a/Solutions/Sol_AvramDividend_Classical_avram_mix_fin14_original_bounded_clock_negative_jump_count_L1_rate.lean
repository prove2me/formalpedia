-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin14_original_bounded_clock_negative_jump_count_L1_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:34:19.652855+00:00
-- url     : https://prove2.me/submissions/f082f58d-e4e9-47de-b8f1-65020d13a0b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual count of negative jumps before any bounded random clock has finite expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ∂P) < ⊤ := by
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hPoint (ω : Ω) :
      J ω (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ≤
      J ω (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) := by
    apply measure_mono
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (hBound ω)⟩, hp.2⟩
  have hRate :
      (∫⁻ ω, J ω (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) ∂P) =
        ((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    simpa only [J, tsub_zero] using
      avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
        X 0 (n : ℝ≥0) (by exact zero_le)
          (Iio (0 : ℝ)) measurableSet_Iio
  have hUpper :
      (∫⁻ ω, J ω (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ∂P) ≤
        ((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    calc
      _ ≤ ∫⁻ ω, J ω (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ)) ∂P :=
        lintegral_mono hPoint
      _ = _ := hRate
  change (∫⁻ ω, J ω (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ∂P) < ⊤
  exact lt_of_le_of_lt hUpper
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) hFinite))
