-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:39:48.137466+00:00
-- url     : https://prove2.me/submissions/65e58fba-5814-47f1-9bcd-2e03451e8a00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    Measurable (fun ω => (K ω : ℝ)) := by
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let K : Ω → ℕ := fun ω =>
    ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change Measurable (fun ω => (K ω : ℝ))
  have hN : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (by simp) B measurableSet_Iic
  have hNr : Measurable (fun ω => (N ω).toReal) :=
    ENNReal.measurable_toReal.comp hN
  have hPoly : Measurable (fun ω =>
      ((N ω).toReal * ((N ω).toReal - 1)) / 2) :=
    (hNr.mul (hNr.sub measurable_const)).div_const 2
  have hEq : (fun ω => (K ω : ℝ)) =
      (fun ω => ((N ω).toReal * ((N ω).toReal - 1)) / 2) := by
    funext ω
    have hfac :=
      avram_p4_f_assembly_original_negative_band_real_factorial_pair X ω T n
    change (N ω).toReal * ((N ω).toReal - 1) = 2 * (K ω : ℝ) at hfac
    linarith
  rw [hEq]
  exact hPoly
