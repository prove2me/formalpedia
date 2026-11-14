-- Prove2me | solution 1 for ConsistentSubmodular.high_anchor_strict_relay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:06.168207+00:00
-- url     : https://prove2.me/submissions/f202ee41-d681-46c3-a383-2515446d606a

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Theorems.Thm_ConsistentSubmodular_relayError_nonpos_of_baseline
import Theorems.Thm_ConsistentSubmodular_high_anchor_low_baseline_error
import Theorems.Thm_ConsistentSubmodular_high_anchor_gap

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
    (hd : 0 < d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b) (hq1 : 1 ≤ q)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    ∀ z : ℝ, (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  have hq3 : q < 3 := by
    by_contra hn
    have := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hden.le
    linarith
  have hwD := (high_anchor_gap d p δ w b q hd hd7 hp hcredit hδ hb hq1 hq3 hatt hfail).le
  have hq : 0 < q := by linarith
  have hbupper : b ≤ 2 * (1 - d) - w := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (show 2 * (1 - d) - b - w ≤ 0 by linarith) hq.le
    linarith
  have he : relayError (1 - d) (3 * d) b w ≤ 0 := by
    by_cases hLD : 3 * d ≤ p + d
    · exact relayError_nonpos_of_baseline _ _ _ _ (by positivity) hwD
        (by linarith) (hLD.trans hb) hbupper
    · have hc : d ≤ p * (1 - p) := by
        rcases hcredit with h | h
        · linarith
        · exact h
      have hL := high_anchor_low_baseline_error d p hd.le hd7 hp (by linarith) hc
      have hslope : 3 * d - 2 * (p + d) ≤ 0 := by nlinarith [sq_nonneg p]
      have hmove := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hwD) hslope
      have hlow : relayError (1 - d) (3 * d) (p + d) w ≤ 0 := by
        unfold relayError at *
        nlinarith only [hL, hmove]
      have hhigh := relayError_upper_endpoint (1 - d) (3 * d) w
        (by positivity) hwD (by linarith)
      have hh := quadratic_nonpositive_between (-(2 * (1 - d) + 2 * w - 3 * d))
        (3 * d * ((1 - d) + w)) (p + d) (2 * (1 - d) - w) b hb hbupper
        (by unfold relayError at hlow; nlinarith only [hlow])
        (by unfold relayError at hhigh; nlinarith only [hhigh])
      unfold relayError
      nlinarith only [hh]
  have hm := credit_to_strict_determinant (1 - d) (3 * d) δ w b q hden hatt
    (by linarith) he
  have hdisc : (δ + (1 - d - δ - w)) ^ 2 <
      (4 * (1 - d) - 3) * (1 - d - δ - w) := by nlinarith only [hm]
  have hr0 : 0 < 1 - d - δ - w := by
    have hrnonneg : 0 ≤ 1 - d - δ - w := by linarith
    nlinarith [sq_nonneg (δ + (1 - d - δ - w))]
  exact strict_edge_of_discriminant (1 - d) δ (1 - d - δ - w) hr0 hdisc

end
