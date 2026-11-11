-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys74_original_no_physical_jumps_path_equals_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:40:35.310118+00:00
-- url     : https://prove2.me/submissions/4391aa08-c0f8-4f5c-8388-38c2d698e57b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys71_original_no_intrinsic_mark_path_equals_drift
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- If every actual original increment jump through the horizon vanishes,
then so does each term of its intrinsic removed-jump source series. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift := by
  filter_upwards [avram_bvb_phys71_original_no_intrinsic_mark_path_equals_drift
    X hX hBV T] with ω hraw
  intro hNoJump
  apply hraw
  intro t ht
  have hzero : ∀ v : ℝ≥0,
      (if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else (0 : ℝ)) = 0 := by
    intro v
    split_ifs with hv
    · have hj := hNoJump v hv.1 (hv.2.trans ht)
      linarith
    · rfl
  simp only [hzero, tsum_zero]
