-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_source_taylor_generator_kernel_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:10:32.840463+00:00
-- url     : https://prove2.me/submissions/1b5e3534-f72a-4fc8-ad0b-4332d271e735

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual controlled prepayment source-jump Taylor remainder is the
localised Lévy generator integrand for every negative mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    (if Y p ∈ Icc (u + δ) v then
      w (Y p + z) - w (Y p) else 0) -
    (if -1 < z then
      z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
      else 0) =
    if Y p ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0 := by
  dsimp only
  let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
  change
    (if Y p ∈ Icc (u + δ) v then
      w (Y p + z) - w (Y p) else 0) -
    (if -1 < z then
      z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
      else 0) =
    if Y p ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0
  by_cases hb : Y p ∈ Icc (u + δ) v
  · by_cases hs : -1 < z
    · have hzI : z ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hs, lt_trans hz (by norm_num)⟩
      simp [hb, hs, SpectrallyNegativeLevy.generatorIntegrand,
        Set.indicator_of_mem hzI]
      ring
    · have hzNI : z ∉ Ioo (-1 : ℝ) 1 := by
        intro h
        exact hs h.1
      simp [hb, hs, SpectrallyNegativeLevy.generatorIntegrand,
        Set.indicator_of_notMem hzNI]
  · simp [hb]
