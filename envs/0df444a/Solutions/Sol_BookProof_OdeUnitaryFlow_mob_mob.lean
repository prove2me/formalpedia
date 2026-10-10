-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.mob_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:47:07.902577+00:00
-- url     : https://prove2.me/submissions/e3164f47-68ff-4788-b247-8d06fb913ce7

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.mob_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_one_add_mul_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (s t x : ℝ) (hx : 1 + t * x ≠ 0) (hst : 1 + (s + t) * x ≠ 0) :
    mob s (mob t x) = mob (s + t) x := by

  have hkey : mob s (mob t x) = mob t x / ((1 + (s + t) * x) / (1 + t * x)) := by
    rw [mob, one_add_mul_mob s t x hx]
  have hx' : 1 + x * t ≠ 0 := by rwa [mul_comm] at hx
  have hst' : 1 + x * (s + t) ≠ 0 := by rwa [mul_comm] at hst
  rw [hkey, mob, mob]
  field_simp
