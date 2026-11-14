-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.before_low_credit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:37.931203+00:00
-- url     : https://prove2.me/submissions/d24059f8-ab7f-4b6e-9fa0-42c6bd035078

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

section

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k q d₀ d p δ : ℝ)
    (hk3 : k < 3) (hq0 : 0 < q) (hq1 : q ≤ 1) (hd : 0 < d) (hd₀ : 0 ≤ d₀)
    (hH : 20 - 11 * k + (2 * k - 5) * q < 0)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hR : 0 ≤ (5 - 3 * q) * d - p - dpoly q * δ) : 0 < V k d₀ d p δ := by
  have hk3p : 0 < 3 - k := sub_pos.mpr hk3
  have hk4p : 0 < 4 - k := by linarith
  let D := dpoly q
  let B := (2 * k - 3) - (2 - k) * D
  let A := (3 - k) * D - (2 * k - 3) * (5 - 3 * q)
  let F := (3 - k) * A + k * B
  have hD : 0 < D := by dsimp [D, dpoly]; nlinarith [sq_nonneg (q - 3 / 2)]
  have hk : 3 / 2 < k := by
    by_contra! hh
    have hh' := mul_nonneg (show 0 ≤ 5 - 2 * k by linarith) (sub_nonneg.mpr hq1)
    nlinarith
  have hdenB : 0 < 11 - 2 * q := by linarith
  have hBid : (11 - 2 * q) * B = -(D + 2) * (20 - 11 * k + (2 * k - 5) * q) + (1 - q) * (1 + q ^ 2) := by
    dsimp [B, D, dpoly]
    ring
  have hB : 0 < B := by
    apply (mul_pos_iff_of_pos_left hdenB).mp
    rw [hBid]
    have hfirst : 0 < -(D + 2) * (20 - 11 * k + (2 * k - 5) * q) :=
      mul_pos_of_neg_of_neg (by linarith) hH
    have hsecond := mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ 1 + q ^ 2 by positivity)
    exact add_pos_of_pos_of_nonneg hfirst hsecond
  have hq3sq : 0 < (q - 3) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hbracket : 0 < 8 * (q - 3) ^ 2 - 9 := by nlinarith [sq_nonneg (q - 1)]
  have hFid : 8 * (q - 3) ^ 2 * F =
      (4 * (q - 3) ^ 2 * (k - 2) + 3 * q) ^ 2 + q ^ 2 * (8 * (q - 3) ^ 2 - 9) := by
    dsimp [F, A, B, D, dpoly]
    ring
  have hF : 0 < F := by
    apply (mul_pos_iff_of_pos_left (show 0 < 8 * (q - 3) ^ 2 by positivity)).mp
    rw [hFid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sq_pos_of_pos hq0) hbracket)
  have hidentity : (3 - k) * D * V k d₀ d p δ =
      ((3 - k) * D + B) * parentFloor k d₀ d p + F * d + 2 * B * (4 - k) * d₀+
      (3 - k) * (2 * k - 3) * ((5 - 3 * q) * d - p - D * δ) := by
    dsimp [V, parentFloor, F, A, B, D, dpoly]
    ring
  have h1 : 0 ≤ ((3 - k) * D + B) * parentFloor k d₀ d p := by positivity
  have h2 : 0 < F * d := mul_pos hF hd
  have h3 : 0 ≤ 2 * B * (4 - k) * d₀ := by positivity
  have h4 : 0 ≤ (3 - k) * (2 * k - 3) * ((5 - 3 * q) * d - p - D * δ) := by
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hR
  have hp : 0 < (3 - k) * D * V k d₀ d p δ := by rw [hidentity]; linarith only [h1, h2, h3, h4]
  exact (mul_pos_iff_of_pos_left (show 0 < (3 - k) * D by positivity)).mp hp

end
