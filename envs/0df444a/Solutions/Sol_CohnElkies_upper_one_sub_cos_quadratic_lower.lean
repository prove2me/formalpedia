-- Prove2me | solution 1 for CohnElkies.upper_one_sub_cos_quadratic_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/55075bb0-dc8c-49ab-a56d-c4d8a36d28d6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_cos_le_quartic

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 / 4 ≤ 1 - Real.cos x := by
  have hnonnegative : 0 ≤ |x| := abs_nonneg x
  have hquartic := cos_le_quartic hnonnegative hx
  rw [Real.cos_abs] at hquartic
  have hsquare : |x| ^ 2 = x ^ 2 := by
    exact sq_abs x
  have hfourth : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [hsquare]
      _ = x ^ 4 := by ring
  rw [hsquare, hfourth] at hquartic
  have hx2 : x ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ hnonnegative hx 2
    simpa [hsquare] using! h
  have hx4 : x ^ 4 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x)
      (sub_nonneg.mpr hx2)]
  nlinarith
end CohnElkies
