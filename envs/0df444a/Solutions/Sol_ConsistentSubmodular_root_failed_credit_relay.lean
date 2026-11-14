-- Prove2me | solution 1 for ConsistentSubmodular.root_failed_credit_relay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:24.376218+00:00
-- url     : https://prove2.me/submissions/f5618317-6728-4660-afd7-b325c47f594b

import Mathlib

section

namespace ConsistentSubmodular

/-- A strict discriminant certificate certifies every point of a relay edge. -/
theorem strict_edge_of_discriminant (A e r : ℝ) (hr : 0 < r)
    (hdisc : (e + r) ^ 2 < (4 * A - 3) * r) (z : ℝ) :
    (3 : ℝ) / 4 < A - e * z - r * z * (1 - z) := by
  have hid :
      4 * r * (A - e * z - r * z * (1 - z) - 3 / 4) =
        (2 * r * z - (e + r)) ^ 2 + (4 * A - 3) * r - (e + r) ^ 2 := by
    ring
  nlinarith [sq_nonneg (2 * r * z - (e + r))]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (δ w v vc k : ℝ)
    (_hδ : 0 ≤ δ) (_hw : 0 ≤ w) (hden : 0 < δ + w)
    (hk : 0 < k) (hvw : w ≤ v) (hvc : v ≤ vc)
    (hatt : k * (δ + w) = 4 * w - v)
    (hfail : vc < 2 - 3 / k) :
    δ < w * (1 - w) ∧
      ∀ z : ℝ, (3 : ℝ) / 4 <
        1 - δ * z - (1 - δ - w) * z * (1 - z) := by
  have hwpos : 0 < w := by
    have := mul_pos hk hden
    linarith
  have hfail' : k * vc < 2 * k - 3 := by
    have := (mul_lt_mul_of_pos_left hfail hk)
    have hid : k * (2 - 3 / k) = 2 * k - 3 := by
      field_simp
    rwa [hid] at this
  have hkw : 3 < k * (2 - w) := by
    have := mul_le_mul_of_nonneg_left (hvw.trans hvc) (le_of_lt hk)
    nlinarith
  have hdelta : δ < w * (1 - w) := by
    by_contra hn
    have hdn : w * (1 - w) ≤ δ := le_of_not_gt hn
    have h1 := mul_le_mul_of_nonneg_left hdn (le_of_lt hk)
    have h2 := mul_lt_mul_of_pos_right hkw hwpos
    nlinarith
  refine ⟨hdelta, ?_⟩
  have hr : 0 < 1 - δ - w := by
    nlinarith [sq_nonneg (1 - w)]
  intro z
  apply strict_edge_of_discriminant 1 δ (1 - δ - w) hr
  nlinarith

end
