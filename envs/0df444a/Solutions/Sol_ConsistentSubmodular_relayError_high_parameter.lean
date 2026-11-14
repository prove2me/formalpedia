-- Prove2me | solution 1 for ConsistentSubmodular.relayError_high_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:41.710785+00:00
-- url     : https://prove2.me/submissions/090a403c-d31e-4864-a2ff-fa600397e51c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Theorems.Thm_ConsistentSubmodular_relayError_nonpos_of_baseline
import Theorems.Thm_ConsistentSubmodular_high_relay_cubic_nonpositive

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

theorem relayError_low_baseline (d p w : ℝ)
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hcredit : d ≤ p * (1 - p))
    (hw : 2 * ((p + d) + 3 * d) / 3 ≤ w) :
    relayError (1 - d) (3 * d) (p + d) w ≤ 0 := by
  have hpd : d ≤ p := by nlinarith [sq_nonneg p]
  have hslope : 3 * d - 2 * (p + d) ≤ 0 := by linarith
  have hmove := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hw) hslope
  have hcoef : 0 ≤ 7 * p + 3 + 17 * (p * (1 - p) + d) := by
    have hp1 : 0 ≤ 1 - p := by linarith
    positivity
  have hinc := mul_nonneg (sub_nonneg.mpr hcredit) hcoef
  have hcubic := mul_nonpos_of_nonneg_of_nonpos hp (high_relay_cubic_nonpositive p hp hp2)
  unfold relayError
  nlinarith only [hmove, hinc, hcubic]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (d p b w : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hDw : 3 * d ≤ w) (hwA : w ≤ 1 - d)
    (hbL : p + d ≤ b) (hb : b ≤ 2 * (1 - d) - w)
    (hw : 2 * ((p + d) + 3 * d) / 3 ≤ w) :
    relayError (1 - d) (3 * d) b w ≤ 0 := by
  by_cases hLD : 3 * d ≤ p + d
  · exact relayError_nonpos_of_baseline _ _ _ _ (by positivity) hDw hwA
      (hLD.trans hbL) hb
  · have hp2 : p ≤ 1 / 2 := by linarith
    have hc : d ≤ p * (1 - p) := by
      rcases hcredit with h | h
      · linarith
      · exact h
    have hlow := relayError_low_baseline d p w hd hp hp2 hc hw
    have hhigh := relayError_upper_endpoint (1 - d) (3 * d) w
      (by positivity) hDw hwA
    have h := quadratic_nonpositive_between (-(2 * (1 - d) + 2 * w - 3 * d))
      (3 * d * ((1 - d) + w)) (p + d) (2 * (1 - d) - w) b hbL hb
      (by unfold relayError at hlow; nlinarith only [hlow])
      (by unfold relayError at hhigh; nlinarith only [hhigh])
    unfold relayError
    nlinarith only [h]

end
