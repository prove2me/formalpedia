-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:57:46.33804+00:00
-- url     : https://prove2.me/submissions/44e45c10-cb0a-4901-9e82-8ab23bdd5dcb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (δ r z a : ℝ) (hδ : 0 < δ)
    (hr : δ ≤ |r|) (ha : |a| ≤ δ) (hz : z = r-a) :
    1+|r|+z^2/2 ≤ (1/δ^2+1/δ+2)*r^2 := by
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have har : |a| ≤ |r| := le_trans ha hr
  have hzr : |z| ≤ 2*|r| := by
    rw [hz]
    have hh := abs_sub r a
    linarith
  have hsqabsr : |r|^2 = r^2 := sq_abs _
  have hsqabsz : |z|^2 = z^2 := sq_abs _
  have hsqr : δ^2 ≤ r^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg (abs_nonneg r) hδ.le)
    nlinarith
  have hone : (1:ℝ) ≤ r^2/δ^2 := by
    apply (le_div_iff₀ hδ2).2
    nlinarith
  have hrmod : |r| ≤ r^2/δ := by
    apply (le_div_iff₀ hδ).2
    have hpr := mul_le_mul_of_nonneg_right hr (abs_nonneg r)
    nlinarith
  have hsqz : z^2 ≤ 4*r^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hzr)
      (add_nonneg (abs_nonneg z) (by positivity : 0 ≤ 2*|r|))
    nlinarith
  calc
    1+|r|+z^2/2 ≤ r^2/δ^2+r^2/δ+2*r^2 := by
      nlinarith
    _ = (1/δ^2+1/δ+2)*r^2 := by ring
