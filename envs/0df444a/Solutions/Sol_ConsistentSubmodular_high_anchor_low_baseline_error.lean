-- Prove2me | solution 1 for ConsistentSubmodular.high_anchor_low_baseline_error
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:48.960443+00:00
-- url     : https://prove2.me/submissions/8dad9abc-8b77-40d7-bd57-bff6c4ee51e8

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Theorems.Thm_ConsistentSubmodular_high_anchor_cubic_nonpositive

section

namespace ConsistentSubmodular

/-- A convex monic quadratic is nonpositive between nonpositive endpoints. -/
theorem quadratic_nonpositive_between (c d l u x : ℝ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : l ^ 2 + c * l + d ≤ 0) (hu : u ^ 2 + c * u + d ≤ 0) :
    x ^ 2 + c * x + d ≤ 0 := by
  by_cases h : x + l + c ≤ 0
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlx) h]
  · have hp : 0 ≤ x + u + c := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) hp]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (d p : ℝ)
    (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p) (hp2d : p ≤ 2 * d)
    (hcredit : d ≤ p * (1 - p)) :
    relayError (1 - d) (3 * d) (p + d) (3 * d) ≤ 0 := by
  by_cases hp9 : p ≤ 9 / 40
  · have hp1 : 0 ≤ 1 - p := by linarith
    have hcoef : 0 ≤ p + 1 + 6 * (p * (1 - p) + d) := by positivity
    have hinc := mul_nonneg (sub_nonneg.mpr hcredit) hcoef
    have hpoly := mul_nonpos_of_nonneg_of_nonpos hp (high_anchor_cubic_nonpositive p hp hp9)
    unfold relayError
    nlinarith only [hinc, hpoly]
  · have hpoly : p ^ 2 - (73 / 40 : ℝ) * p + 287 / 800 ≤ 0 := by
      have h := quadratic_nonpositive_between (-(73 / 40 : ℝ)) (287 / 800)
        (9 / 40) (7 / 20) p (by linarith) (by linarith) (by norm_num) (by norm_num)
      nlinarith only [h]
    have hcoef : 0 ≤ p + 1 + 6 * (7 / 40 + d) := by positivity
    have hinc := mul_nonneg (sub_nonneg.mpr hd7) hcoef
    unfold relayError
    nlinarith only [hinc, hpoly]

end
