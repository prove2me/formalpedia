-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_nearzero_variance_formula_forces_zero_band_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:11:00.321542+00:00
-- url     : https://prove2.me/submissions/8b066997-4261-4bb3-b4e5-0f47af6c042a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- At cutoff zero the physical retained smallband is empty; the nearzero formula then forces zero smallmark energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hNear : ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
        (t : ℝ) *
          (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) = 0 := by
  have hzero :
      (∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 1 ω = 0) := by
    intro ω
    simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  have h0 := hNear 0 1
  simpa [hzero] using h0.symm
