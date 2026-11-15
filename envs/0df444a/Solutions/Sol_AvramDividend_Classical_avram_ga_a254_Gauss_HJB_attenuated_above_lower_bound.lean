-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a254_Gauss_HJB_attenuated_above_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:37.827298+00:00
-- url     : https://prove2.me/submissions/99d26823-ea95-4557-8c64-51a3ab6f63e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (g0 g e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hga : g0 ≤ g) : -|g0| ≤ e*g := by
  have ha : 0 ≤ (1-e)*|g0| :=
    mul_nonneg (by linarith) (abs_nonneg _)
  have hb : 0 ≤ e*(g0+|g0|) :=
    mul_nonneg he0 (by linarith [neg_abs_le g0])
  have hc : 0 ≤ e*(g-g0) :=
    mul_nonneg he0 (sub_nonneg.mpr hga)
  nlinarith
