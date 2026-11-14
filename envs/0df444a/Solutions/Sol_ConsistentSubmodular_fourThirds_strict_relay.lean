-- Prove2me | solution 1 for ConsistentSubmodular.fourThirds_strict_relay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:29.177196+00:00
-- url     : https://prove2.me/submissions/d98d33f6-55db-46c6-9ed9-975603801ad1

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Theorems.Thm_ConsistentSubmodular_relayError_nonpos_of_baseline
import Theorems.Thm_ConsistentSubmodular_fourThirds_low_baseline_relay

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
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (_hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b)
    (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hatt : (3 - q) * w = q * δ + b + 3 * d)
    (hfail : q * (b + w) < 2 * (1 - d) * q - 3 * (1 - 4 * d)) :
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  have hqpos : 0 < q := by linarith
  by_cases hLD : 3 * d ≤ p + d
  · have hDw : 3 * d ≤ w := by
      have h1 := mul_nonneg (show 0 ≤ q - 1 by linarith) hw
      have h2 := mul_nonneg hqpos.le hδ
      nlinarith
    have hbupper : b ≤ 2 * (1 - d) - w := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos hqpos.le
        (show 2 * (1 - d) - b - w ≤ 0 by linarith)
      nlinarith
    have he := relayError_nonpos_of_baseline (1 - d) (3 * d) b w
      (by positivity) hDw (by linarith) (hLD.trans hb) hbupper
    have hm := credit_to_strict_determinant (1 - d) (3 * d) δ w b q hden
      (by nlinarith only [hatt]) (by nlinarith only [hfail]) he
    have hdisc : (δ + (1 - d - δ - w)) ^ 2 <
        (4 * (1 - d) - 3) * (1 - d - δ - w) := by nlinarith only [hm]
    have hr0 : 0 < 1 - d - δ - w := by
      have hrnonneg : 0 ≤ 1 - d - δ - w := by linarith
      nlinarith [sq_nonneg (δ + (1 - d - δ - w))]
    exact fun z _ _ => strict_edge_of_discriminant (1 - d) δ (1 - d - δ - w) hr0 hdisc z
  · have hc : d ≤ p * (1 - p) := by
      rcases hcredit with h | h
      · linarith
      · exact h
    have hp0 : 0 < p := by nlinarith [sq_nonneg p]
    have hp2 : p ≤ 1 / 2 := by linarith
    have hfail' : b + w < 2 * (1 - d) - 3 * (1 - 4 * d) / q := by
      have hid : q * (2 * (1 - d) - 3 * (1 - 4 * d) / q) =
          2 * (1 - d) * q - 3 * (1 - 4 * d) := by field_simp
      nlinarith
    intro z hz hz1
    have hs := fourThirds_low_baseline_relay p d q δ w b z hp0 hp2 (by linarith)
      hd4 hc hq hq2 hδ hb hatt hfail' hz hz1
    linarith

end
