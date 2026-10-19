-- Prove2me | solution 1 for CohnElkies.upper_shortShell_oscillation_div_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/0ce684d1-6465-4ba8-9a9a-4678fdb11822

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_one_sub_cos_le_min

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
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
      min (T ^ 2) ((a ^ 2)⁻¹) := by
  have hden : 0 < 2 * a ^ 2 := by positivity
  have hcos := upper_one_sub_cos_le_min (a * T)
  apply le_min
  · calc
      (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
          ((a * T) ^ 2 / 2) / (2 * a ^ 2) :=
        div_le_div_of_nonneg_right
          (hcos.trans (min_le_left _ _)) hden.le
      _ = T ^ 2 / 4 := by
        field_simp [ha.ne']; ring
      _ ≤ T ^ 2 := by
        nlinarith [sq_nonneg T]
  · calc
      (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤
          2 / (2 * a ^ 2) :=
        div_le_div_of_nonneg_right
          (hcos.trans (min_le_right _ _)) hden.le
      _ = (a ^ 2)⁻¹ := by
        field_simp [ha.ne']
end CohnElkies
