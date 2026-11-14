-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a143_true_crossing_discount_positive_value_HJB_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:32.063194+00:00
-- url     : https://prove2.me/submissions/e206e31c-6994-4096-a22a-8686b3291b8e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- A genuine clipped source crossing value positive HJB error requires only an upper positive endpoint envelope, a compact lower initial value and absolute compensation. -/
theorem solution
    (E Wafter Wbefore H T B : ℝ)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hUpper : Wafter ≤ T) (hLower : -B ≤ Wbefore) :
    max (E * (Wafter - Wbefore) - H) 0 ≤
      T + B + |H| := by
  have hDiff : Wafter - Wbefore ≤ T + B := by linarith
  have hWeight : E * (Wafter - Wbefore) ≤ E * (T + B) :=
    mul_le_mul_of_nonneg_left hDiff hE0
  have hScale : E * (T + B) ≤ T + B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hE1) (add_nonneg hT hB)]
  apply max_le
  · linarith [hWeight, hScale, neg_le_abs H]
  · linarith [abs_nonneg H]
