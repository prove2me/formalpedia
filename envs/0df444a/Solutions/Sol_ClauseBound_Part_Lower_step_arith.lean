-- Prove2me | solution 1 for ClauseBound.Part.Lower.step_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:32:42.747178+00:00
-- url     : https://prove2.me/submissions/a0ea2cbe-25a8-49e9-8922-744e23a5da5e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {c s B α γ Z : ℝ} {K : ℕ} (hc : 0 < c) (hB : 3890 ≤ B) (hs : 4 * B / c + c ≤ s) (hα : α = c / (2 * s) - B / s ^ 2)
    (hγ : γ = c / (2 * s ^ 3)) (hZ : Z = c ^ 2 / 4) (hK1 : 1 / α ≤ K) (hK2 : (K : ℝ) ≤ 1 / α + 1) :
    s ^ 2 ≤ 1 / α ^ 2 * (Z - 1 / K) - K / 4 - 486 * γ / α ^ 4 * Z := by
  have hBc : 0 < 4 * B / c := by positivity
  have hs0 : 0 < s := by linarith
  have hsc : c ≤ s := by linarith
  have hcs : 4 * B ≤ c * s := by
    have : 4 * B / c ≤ s := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  obtain ⟨q, hq⟩ : ∃ q, q = c * s - 2 * B := ⟨_, rfl⟩
  have hq0 : 0 < q := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = 2 * s ^ 2 / q := ⟨_, rfl⟩
  have hαw : α = 1 / w := by
    rw [hα, hw, hq]
    have : c * s - 2 * B ≠ 0 := by linarith
    field_simp
  have hw0 : 0 < w := by rw [hw]; positivity
  have e1 : 1 / α = w := by rw [hαw]; field_simp
  have e2 : 1 / α ^ 2 = w ^ 2 := by rw [hαw]; field_simp
  have e4 : 486 * γ / α ^ 4 = 486 * γ * w ^ 4 := by rw [hαw]; field_simp
  rw [e1] at hK1 hK2
  rw [e2, e4]
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le hw0 hK1
  -- the gain
  have g1 : s ^ 2 + 4 * B * s / c ≤ w ^ 2 * Z := by
    rw [hw, hZ]
    have e5 : (2 * s ^ 2 / q) ^ 2 * (c ^ 2 / 4) = c ^ 2 * s ^ 4 / q ^ 2 := by field_simp; ring
    rw [e5, le_div_iff₀ (by positivity)]
    have e6 : (s ^ 2 + 4 * B * s / c) * q ^ 2 = s * ((c * s + 4 * B) * q ^ 2) / c := by field_simp
    rw [e6, div_le_iff₀ hc, hq]
    have h7 : (c * s + 4 * B) * (c * s - 2 * B) ^ 2 ≤ (c * s) ^ 3 := by nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ B) (by linarith : (0:ℝ) ≤ B)) (by linarith : (0:ℝ) ≤ 12 * (c * s) - 16 * B)]
    calc s * ((c * s + 4 * B) * (c * s - 2 * B) ^ 2) ≤ s * (c * s) ^ 3 := by gcongr
      _ = c ^ 2 * s ^ 4 * c := by ring
  -- the losses
  have l1 : w ≤ 4 * s / c := by
    rw [hw, div_le_div_iff₀ hq0 hc, hq]
    nlinarith
  have l2 : w ^ 2 * (1 / K) ≤ w := by
    have : 1 / (K : ℝ) ≤ 1 / w := one_div_le_one_div_of_le hw0 hK1
    calc w ^ 2 * (1 / K) ≤ w ^ 2 * (1 / w) := by gcongr
      _ = w := by field_simp
  have l3 : 486 * γ * w ^ 4 * Z ≤ 15552 * s / c := by
    have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    calc 486 * γ * w ^ 4 * Z ≤ 486 * γ * (4 * s / c) ^ 4 * Z := by gcongr
      _ = 15552 * s / c := by rw [hγ, hZ]; field_simp; norm_num
  have l4 : 1 ≤ s / c := by rwa [le_div_iff₀ hc, one_mul]
  have l5 : 4 * B * s / c = 4 * B * (s / c) := by ring
  have l6 : 4 * s / c = 4 * (s / c) := by ring
  have l7 : 15552 * s / c = 15552 * (s / c) := by ring
  have l8 : 15560 * (s / c) ≤ 4 * B * (s / c) := by
    have : (0 : ℝ) ≤ s / c := by positivity
    nlinarith
  nlinarith
end ClauseBound.Part.Lower
