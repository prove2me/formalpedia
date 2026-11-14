-- Prove2me | solution 1 for AvramDividend.Classical.avram_b81_original_jumpfree_cell_large_mark_sum_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:06:01.874223+00:00
-- url     : https://prove2.me/submissions/ebc79f2a-20be-4292-87af-f4c38e0ea5af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original large negative mark source sum is identical at the two endpoints of a no-jump physical interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω := by
  obtain ⟨Ft, hFt, hCt⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
      X ω t
  obtain ⟨Fs, hFs, hCs⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
      X ω s
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
        have hneg : (0 : ℝ) ≤ -1 := by
          simpa only [hz] using hu'.2.2
        linarith
      exact (hFs u).2 ⟨hu'.1, hus, hu'.2.2⟩
    · intro hu
      have hu' := (hFs u).1 hu
      exact (hFt u).2 ⟨hu'.1, hu'.2.1.trans hst, hu'.2.2⟩
  rw [hFinset] at hCt
  exact hCt.trans hCs.symm
