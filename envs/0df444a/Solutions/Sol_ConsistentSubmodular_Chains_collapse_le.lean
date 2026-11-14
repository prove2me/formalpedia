-- Prove2me | solution 1 for ConsistentSubmodular.Chains.collapse_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:59.365056+00:00
-- url     : https://prove2.me/submissions/ec4aee03-c1b8-4688-82e3-cb5c16b475dd

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_bounds

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem one_sub_qStar_pos : 0 < 1 - qStar := by linarith [qStar_bounds.2]

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x)
    (hxL : x ≤ collapseBound) : edgeValue x y + edgeValue y z ≤ edgeValue x z := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 - qStar ≤ 1 / x := by
    rw [collapseBound, le_div_iff₀ one_sub_qStar_pos] at hxL
    rw [le_div_iff₀ hx0]
    linarith
  have hid : edgeValue x y + edgeValue y z - edgeValue x z =
      (y - z) * (1 / y - 1 / x) - qStar * (y - 1) := by
    unfold edgeValue
    field_simp
    ring
  have ha : 0 ≤ 1 / y - 1 / x := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hy0 hyx
  have hb : 1 / y ≤ 1 := by
    rw [div_le_one hy0]
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hz) ha, mul_nonneg (show 0 ≤ y - 1 by linarith)
    (sub_nonneg.mpr hb), mul_nonneg (show 0 ≤ y - 1 by linarith) (sub_nonneg.mpr hx1)]

end
