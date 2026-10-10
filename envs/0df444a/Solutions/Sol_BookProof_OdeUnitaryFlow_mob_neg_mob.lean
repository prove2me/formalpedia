-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.mob_neg_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:04.459566+00:00
-- url     : https://prove2.me/submissions/afb71a02-0df1-405d-b814-71e70fd2e8b2

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.mob_neg_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_neg_mul_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t x : ℝ) (hx : x ∈ flowDom t) : mob (-t) (mob t x) = x := by

  have h : 1 + t * x ≠ 0 := hx
  have hkey : mob (-t) (mob t x) = mob t x / (1 + t * x)⁻¹ := by
    rw [mob, one_add_neg_mul_mob t x hx]
  rw [hkey, mob, div_eq_iff (inv_ne_zero h), div_eq_mul_inv]
