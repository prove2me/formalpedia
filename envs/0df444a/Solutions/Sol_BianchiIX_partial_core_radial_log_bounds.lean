-- Prove2me | solution 1 for BianchiIX.partial_core_radial_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:48.355821+00:00
-- url     : https://prove2.me/submissions/0b035e3c-ecfd-4383-b5a1-453d191549f9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {r K k B L Q dz lU lP : ℝ}
    (hr : 0 < r) (hK : 1 ≤ K) (hk : 0 < k) (hB : 0 ≤ B) (hL : 1 ≤ L)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hQ : Q ≤ 5 * K ^ 2 / r ^ 2) (hdz : |dz| ≤ K / r)
    (hU : |lU| ≤ 40 * B * L * Q + 2 * k * |dz|)
    (hP : |lP| ≤ 236 * B * L * Q / k ^ 2 + 4 * |dz| / k) :
    |lU| ≤ (200 * B + 2) * K ^ 2 * L / r ^ 2 ∧
      |lP| ≤ (1180 * B * K ^ 4 + 4 * K ^ 2) * L := by
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have HU : 40 * B * L * Q ≤ 200 * B * K ^ 2 * L / r ^ 2 :=
    (mul_le_mul_of_nonneg_left hQ (by positivity)).trans_eq (by ring)
  have HUz : 2 * k * |dz| ≤ 2 * K ^ 2 / r ^ 2 := by
    calc
      _ ≤ 2 * (K / r) * (K / r) := by gcongr
      _ = _ := by ring
  have HP : 236 * B * L * Q / k ^ 2 ≤ 1180 * B * K ^ 4 * L := by
    calc
      _ ≤ 236 * B * L * (5 * K ^ 2 / r ^ 2) / k ^ 2 := by gcongr
      _ = (1180 * B * K ^ 2 * L / r ^ 2) * (1 / k) ^ 2 := by ring
      _ ≤ (1180 * B * K ^ 2 * L / r ^ 2) * (K * r) ^ 2 := by gcongr
      _ = _ := by field_simp
  have HPz : 4 * |dz| / k ≤ 4 * K ^ 2 := by
    calc
      _ = 4 * |dz| * (1 / k) := by ring
      _ ≤ 4 * (K / r) * (K * r) := by gcongr
      _ = _ := by field_simp
  constructor
  · have H := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * K ^ 2 / r ^ 2 by positivity)
    have HUz' := HUz.trans (by simpa only [mul_one] using H)
    exact hU.trans ((add_le_add HU HUz').trans_eq (by ring))
  · have H := mul_le_mul_of_nonneg_left hL (show 0 ≤ 4 * K ^ 2 by positivity)
    nlinarith only [hP, HP, HPz, H]
