-- Prove2me | solution 1 for D1Bound5.frontier_quadratic_interval_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:44.276413+00:00
-- url     : https://prove2.me/submissions/ae358444-7ead-498d-8fe5-b2e5d0f99d62

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5









/-- Convex quadratic endpoint exclusion, proved by its chord identity. -/
theorem _root_.solution (a b c lo hi x : ℝ)
    (ha : 0 ≤ a) (hlo : lo < x) (hhi : x ≤ hi)
    (hql : a*lo^2+b*lo+c < 0) (hqh : a*hi^2+b*hi+c < 0)
    (hqx : 0 ≤ a*x^2+b*x+c) : False := by
  have hleft := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hhi) hql.le
  have hright := mul_neg_of_pos_of_neg (sub_pos.mpr hlo) hqh
  have hwidth : 0 ≤ hi-lo := by linarith only [hlo,hhi]
  have hmid := mul_nonneg hwidth hqx
  have hcorr := mul_nonneg (mul_nonneg (mul_nonneg ha hwidth)
    (sub_nonneg.mpr hlo.le)) (sub_nonneg.mpr hhi)
  nlinarith only [hleft,hright,hmid,hcorr]

end D1Bound5
end
