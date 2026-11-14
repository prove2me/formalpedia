-- Prove2me | solution 1 for ConsistentSubmodular.relayError_nonpos_of_baseline
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:25.046062+00:00
-- url     : https://prove2.me/submissions/26cc683c-2569-4283-83ac-aa0a593470d5

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError

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

theorem relayError_upper_endpoint (A D w : ℝ)
    (hD : 0 ≤ D) (hDw : D ≤ w) (hwA : w ≤ A) :
    relayError A D (2 * A - w) w ≤ 0 := by
  have hw : 0 ≤ w := hD.trans hDw
  have hA : 0 ≤ A := hw.trans hwA
  have h1 := mul_nonneg hw (sub_nonneg.mpr hwA)
  have h2 := mul_nonneg hA (sub_nonneg.mpr hDw)
  unfold relayError
  nlinarith

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (A D b w : ℝ)
    (hD : 0 ≤ D) (hDw : D ≤ w) (hwA : w ≤ A)
    (hDb : D ≤ b) (hb : b ≤ 2 * A - w) : relayError A D b w ≤ 0 := by
  have hlow : relayError A D D w ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hD (show 2 * D - A - w ≤ 0 by linarith)
    unfold relayError
    nlinarith
  have hhigh := relayError_upper_endpoint A D w hD hDw hwA
  have h := quadratic_nonpositive_between (-(2 * A + 2 * w - D)) (D * (A + w))
    D (2 * A - w) b hDb hb
    (by unfold relayError at hlow; nlinarith only [hlow])
    (by unfold relayError at hhigh; nlinarith only [hhigh])
  unfold relayError
  nlinarith only [h]

end
