-- Prove2me | solution 1 for AvramDividend.Classical.avram_b80_original_jumpfree_cell_smallband_compensator_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:20:58.095176+00:00
-- url     : https://prove2.me/submissions/c7b360a7-e7dd-474d-9ef8-6b5e48bdba3e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact original compensated small negative band has only its compensator drift on a genuine no-jump interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
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
        have hz := hNoJump u hsu hu'.2.1
        have hneg : -(1 / ((n : ℝ) + 1)) < 0 := by
          have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
            div_pos (by norm_num) hn
          linarith
        have hle : (0 : ℝ) ≤ -(1 / ((n : ℝ) + 1)) := by
          simpa only [hz] using hu'.2.2.2
        exact (not_le_of_gt hneg) hle
      exact (hFs u).2 ⟨hu'.1, hus, hu'.2.2⟩
    · intro hu
      have hu' := (hFs u).1 hu
      exact (hFt u).2 ⟨hu'.1, hu'.2.1.trans hst, hu'.2.2⟩
  simp only [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  rw [hFinset] at hCt
  rw [hCt, hCs]
  ring
