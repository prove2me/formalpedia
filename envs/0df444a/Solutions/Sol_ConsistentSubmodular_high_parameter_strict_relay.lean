-- Prove2me | solution 1 for ConsistentSubmodular.high_parameter_strict_relay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:40.482086+00:00
-- url     : https://prove2.me/submissions/30400e17-76f1-46f4-ac02-ff38e0eda1ec

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Theorems.Thm_ConsistentSubmodular_relayError_high_parameter

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

namespace ConsistentSubmodular

theorem credit_to_strict_determinant (A D δ w b q : ℝ)
    (hden : 0 < δ + w)
    (hatt : q * (δ + w) = 3 * w - b - D)
    (hfail : 3 * (A - D) < (2 * A - b - w) * q)
    (herror : relayError A D b w ≤ 0) :
    0 < (A - w) * (w - D) - (A - D) * δ := by
  have hid :
      (δ + w) * ((2 * A - b - w) * q - 3 * (A - D)) =
        3 * ((A - w) * (w - D) - (A - D) * δ) + relayError A D b w := by
    calc
      _ = (q * (δ + w)) * (2 * A - b - w) - 3 * (A - D) * (δ + w) := by ring
      _ = _ := by rw [hatt]; unfold relayError; ring
  have := mul_pos hden (sub_pos.mpr hfail)
  linarith

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (d p δ w b q : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hw0 : 0 ≤ w) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b)
    (hq : (3 : ℝ) / 2 ≤ q)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    ∀ z : ℝ, (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  have hq0 : 0 < q := by linarith
  have hbudget : 2 * d ≤ p + d := by
    rcases hcredit with h | h
    · linarith
    · nlinarith [sq_nonneg p]
  have hwbound : 2 * ((p + d) + 3 * d) / 3 ≤ w := by
    have h1 := mul_nonneg (show 0 ≤ q - 3 / 2 by linarith) hw0
    have h2 := mul_nonneg hq0.le hδ
    nlinarith
  have hDw : 3 * d ≤ w := by linarith
  have hbupper : b ≤ 2 * (1 - d) - w := by
    by_contra hn
    have hx : 2 * (1 - d) - b - w ≤ 0 := by linarith
    have := mul_nonpos_of_nonpos_of_nonneg hx hq0.le
    linarith
  have he := relayError_high_parameter d p b w hd hd4 hp hcredit hDw
    (by linarith) hb hbupper hwbound
  have hm := credit_to_strict_determinant (1 - d) (3 * d) δ w b q hden hatt
    (by linarith) he
  have hdisc : (δ + (1 - d - δ - w)) ^ 2 <
      (4 * (1 - d) - 3) * (1 - d - δ - w) := by nlinarith only [hm]
  have hr0 : 0 < 1 - d - δ - w := by
    have hrnonneg : 0 ≤ 1 - d - δ - w := by linarith
    nlinarith [sq_nonneg (δ + (1 - d - δ - w))]
  exact strict_edge_of_discriminant (1 - d) δ (1 - d - δ - w) hr0 hdisc

end
