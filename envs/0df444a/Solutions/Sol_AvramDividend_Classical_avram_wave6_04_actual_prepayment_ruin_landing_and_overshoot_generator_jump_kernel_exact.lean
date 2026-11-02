-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_prepayment_ruin_landing_and_overshoot_generator_jump_kernel_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:16:56.080422+00:00
-- url     : https://prove2.me/submissions/cf616f15-0c80-475a-b483-20cc9eb9ffb2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ)
    (p : ℝ≥0 × Ω) :
    let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    Y p ∈ Icc (u + δ) v →
    let R : ℝ :=
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    (R * SpectrallyNegativeLevy.generatorIntegrand w (Y p) (-(Y p)) =
      R * (w 0 - w (Y p) +
        if Y p < 1 then Y p * deriv w (Y p) else 0)) ∧
    (∀ z : ℝ, z < -(Y p) →
      R * SpectrallyNegativeLevy.generatorIntegrand w (Y p) z =
        R * (-w (Y p) -
          if -1 < z then z * deriv w (Y p) else 0)) := by
  classical
  intro Y hy R
  have hypos : 0 < Y p := by linarith [hy.1]
  have hLanding :
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) (-(Y p)) =
        w 0 - w (Y p) +
          (if Y p < 1 then Y p * deriv w (Y p) else 0) := by
    by_cases hsmall : Y p < 1
    · have hmem : -(Y p) ∈ Set.Ioo (-1 : ℝ) 1 := by
        constructor <;> linarith
      simp [SpectrallyNegativeLevy.generatorIntegrand,
        Set.indicator_of_mem hmem, hsmall]
      ring
    · have hnot : -(Y p) ∉ Set.Ioo (-1 : ℝ) 1 := by
        intro h
        exact hsmall (by linarith [h.1])
      simp [SpectrallyNegativeLevy.generatorIntegrand,
        Set.indicator_of_notMem hnot, hsmall]
  have hOvershoot (z : ℝ) (hz : z < -(Y p)) :
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) z =
        -w (Y p) - (if -1 < z then z * deriv w (Y p) else 0) := by
    have hzneg : z < 0 := by linarith
    have hzval : Y p + z < 0 := by linarith
    have hwz : w (Y p + z) = 0 := hw_neg (Y p + z) hzval
    by_cases hsmall : -1 < z
    · have hmem : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
      simp [SpectrallyNegativeLevy.generatorIntegrand,
        Set.indicator_of_mem hmem, hwz, hsmall]
      ring
    · have hnot : z ∉ Set.Ioo (-1 : ℝ) 1 := by
        intro h
        exact hsmall h.1
      simp [SpectrallyNegativeLevy.generatorIntegrand,
        Set.indicator_of_notMem hnot, hwz, hsmall]
  constructor
  · exact congrArg (fun t : ℝ => R * t) hLanding
  · intro z hz
    exact congrArg (fun t : ℝ => R * t) (hOvershoot z hz)