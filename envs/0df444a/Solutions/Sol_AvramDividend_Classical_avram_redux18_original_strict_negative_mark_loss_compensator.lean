-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_original_strict_negative_mark_loss_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:20:40.704913+00:00
-- url     : https://prove2.me/submissions/0ac69b49-e8e1-40c1-a3bc-b5511634e032

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux18_original_negative_band_weighted_levy_compensator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original strict-cutoff mean mark loss with the exact Levy compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) :
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (T : ℝ≥0∞) * (∫⁻ y in B, φ y ∂X.ν) := by
  let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
  let B : Set ℝ := Iio (-ε)
  change (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (T : ℝ≥0∞) * (∫⁻ y in B, φ y ∂X.ν)
  have hφ : Measurable φ :=
    (measurable_const.sub Real.measurable_exp).ennreal_ofReal
  have hg : Measurable (B.indicator φ) := hφ.indicator measurableSet_Iio
  have hSupport (y : ℝ) (hy : y ∉ Iic (-ε)) :
      (B.indicator φ) y = 0 := by
    have hnot : y ∉ B := by
      intro h
      have hlt : y < -ε := h
      have hle : y ≤ -ε := le_of_lt hlt
      have hmem : y ∈ Iic (-ε) := Set.mem_Iic.mpr hle
      exact hy hmem
    simp [Set.indicator_of_notMem hnot]
  have h :=
    AvramDividend.Classical.avram_redux18_original_negative_band_weighted_levy_compensator
      X T (B.indicator φ) hg ε hε hSupport
  have hIndicator := MeasureTheory.lintegral_indicator
    (μ := X.ν) (s := B) measurableSet_Iio φ
  rw [hIndicator] at h
  exact h
