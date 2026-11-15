-- Prove2me | solution 1 for AvramDividend.Classical.avram_b130_original_negative_bandfree_cell_exact_compensation_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:32:43.496646+00:00
-- url     : https://prove2.me/submissions/d68a4e75-79ea-4724-9e01-9ba481081194

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original compensated negative-band source has only its signed drift where that physical cutoff band contains no jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hNoBand : ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
      -((t : ℝ) - (s : ℝ)) *
        (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by
  obtain ⟨Ft, hFt, hCt⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω t n
  obtain ⟨Fs, hFs, hCs⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω s n
  have hFinset : Ft = Fs := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      have hu' := (hFt u).1 hu
      have hus : u ≤ s := by
        by_contra hnots
        have hsu : s < u := lt_of_not_ge hnots
        exact False.elim (hNoBand u hsu hu'.2.1 hu'.2.2.2)
      exact (hFs u).2 ⟨hu'.1, hus, hu'.2.2⟩
    · intro hu
      have hu' := (hFs u).1 hu
      exact (hFt u).2 ⟨hu'.1, hu'.2.1.trans hst, hu'.2.2⟩
  simp only [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  rw [hFinset] at hCt
  rw [hCt, hCs]
  ring
