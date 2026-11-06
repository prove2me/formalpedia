-- Prove2me | solution 1 for ExplicitCost.own_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:18:19.530577+00:00
-- url     : https://prove2.me/submissions/80d467b2-6670-43ef-ba62-77245a883912

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Count
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountStep
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines
namespace ExplicitCost
theorem _root_.solution {Y Z T s u a κ q t : ℝ} (hY : 1 ≤ Y) (hZ : 8 ≤ Z) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    a * (Y * κ) + q + Y + a * ((s * Y * (u + 2) + s * Y * t + 2) * T + 2) ≤ a * ((κ + t * T * s * (u * (Y * Z))) * Y + 2 * Y) + q + Y := by
  obtain ⟨w, hw⟩ : ∃ w, w = s * Y * (u * t) := ⟨_, rfl⟩
  have hut : 1 ≤ u * t := one_le_mul_of_one_le_of_one_le hu ht
  have hsY : 1 ≤ s * Y := one_le_mul_of_one_le_of_one_le hs hY
  have hw1 : 1 ≤ w := by rw [hw]; exact one_le_mul_of_one_le_of_one_le hsY hut
  have h1 : u + 2 + t ≤ 4 * (u * t) := by nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 ht)]
  have h2 : s * Y * (u + 2) + s * Y * t + 2 ≤ 6 * w := by
    have a1 : s * Y * (u + 2 + t) ≤ s * Y * (4 * (u * t)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have e1 : s * Y * (u + 2) + s * Y * t = s * Y * (u + 2 + t) := by ring
    have e2 : s * Y * (4 * (u * t)) = 4 * w := by rw [hw]; ring
    linarith
  have h3 : 6 * w ≤ Z * Y * w := by
    have a1 : (8 : ℝ) * 1 ≤ Z * Y := mul_le_mul hZ hY (by norm_num) (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h4 : (s * Y * (u + 2) + s * Y * t + 2) * T ≤ Z * Y * w * T := mul_le_mul_of_nonneg_right (h2.trans h3) (by linarith)
  have h5 : (s * Y * (u + 2) + s * Y * t + 2) * T + 2 ≤ t * T * s * (u * (Y * Z)) * Y + 2 * Y := by
    have e : t * T * s * (u * (Y * Z)) * Y = Z * Y * w * T := by rw [hw]; ring
    rw [e]
    linarith
  have h6 := mul_le_mul_of_nonneg_left h5 ha
  have e : a * ((κ + t * T * s * (u * (Y * Z))) * Y + 2 * Y) = a * (Y * κ) + a * (t * T * s * (u * (Y * Z)) * Y + 2 * Y) := by ring
  rw [e]
  linarith
end ExplicitCost
