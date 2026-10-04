-- Prove2me | solution 2 for FreyPackage.freyCurveInt_discr_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T12:12:42.800854+00:00
-- url     : https://prove2.me/submissions/543d79e3-1847-43b8-b587-de8d5bee7143

import Theorems.Thm_FreyPackage_freyCurveInt_map
import Theorems.Thm_FreyPackage_freyCurve_discriminant
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (P : FreyPackage) : P.freyCurveInt.Δ ≠ 0 := by
  have habc : (P.a : ℚ) * P.b * P.c ≠ 0 := by
    exact_mod_cast P.habc0
  have hΔ : P.freyCurve.Δ ≠ 0 := by
    rw [P.freyCurve_discriminant]
    exact div_ne_zero (pow_ne_zero _ habc) (by norm_num)
  intro hzero
  apply hΔ
  rw [← P.freyCurveInt_map, WeierstrassCurve.map_Δ]
  simp only [hzero, map_zero]
