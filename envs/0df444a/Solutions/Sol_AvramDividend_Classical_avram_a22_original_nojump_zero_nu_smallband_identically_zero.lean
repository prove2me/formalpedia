-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_nojump_zero_nu_smallband_identically_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:49:50.1364+00:00
-- url     : https://prove2.me/submissions/69bff99a-be7d-4869-a2c2-59f9fad1db93

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual original jump counting measure has empty support when every physical jump is zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (n : ℕ) (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω = 0 := by
  have hEmpty :
      {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} =
      ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hu
    exact hu.2 (hNoJump u hu.1)
  simp [avram_p4_h_gaussian_intrinsic_small_band_compensated, hν, hEmpty]
