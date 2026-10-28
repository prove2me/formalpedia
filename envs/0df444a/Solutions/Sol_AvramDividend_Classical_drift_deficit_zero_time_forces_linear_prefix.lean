-- Prove2me | solution 1 for AvramDividend.Classical.drift_deficit_zero_time_forces_linear_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:57:37.319084+00:00
-- url     : https://prove2.me/submissions/e0e6b4eb-05bb-4948-8861-9656ef764907

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.Real.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A drift deficit that is still zero forces a linear whole-path prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hStart : X.X 0 ω = 0)
    (hMono : Monotone (fun t : ℝ≥0 => X.drift * (t : ℝ) - X.X t ω))
    (t : ℝ≥0) (hZero : X.drift * (t : ℝ) - X.X t ω = 0) :
    ∀ s : ℝ≥0, s ≤ t → X.X s ω = X.drift * (s : ℝ) := by
  intro s hs
  have hNonneg : 0 ≤ X.drift * (s : ℝ) - X.X s ω := by
    have h := hMono (show (0 : ℝ≥0) ≤ s from zero_le)
    simpa [hStart] using h
  have hNonpos : X.drift * (s : ℝ) - X.X s ω ≤ 0 := by
    have h := hMono hs
    simpa only [hZero] using h
  exact (sub_eq_zero.mp (le_antisymm hNonpos hNonneg)).symm
