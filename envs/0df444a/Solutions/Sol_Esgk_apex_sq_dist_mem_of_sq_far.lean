-- Prove2me | solution 1 for Esgk.apex_sq_dist_mem_of_sq_far
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:11:08.924656+00:00
-- url     : https://prove2.me/submissions/c34e6cc6-6cf0-421d-b4ab-fbe47175d144

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_Foundation

section

open EuclideanGeometry Esgk
open scoped RealInnerProductSpace

theorem solution {c z a b : Point} {ρ x : ℝ} (hρ : 0 < ρ)
    (hz : ρ ^ 2 * (1 - x) ≤ dist z c ^ 2) (hz1 : dist z c ^ 2 ≤ ρ ^ 2)
    (ha : ρ ^ 2 * (1 - x) ≤ dist a c ^ 2) (ha1 : dist a c ^ 2 ≤ ρ ^ 2)
    (hb : ρ ^ 2 * (1 - x) ≤ dist b c ^ 2) (hb1 : dist b c ^ 2 ≤ ρ ^ 2)
    (hab : 3 * ρ ^ 2 < dist a b ^ 2) (heq : dist z a = dist z b) :
    ρ ^ 2 * (1 - 2 * x) < dist z a ^ 2 ∧ dist z a ^ 2 < 3 * ρ ^ 2 := by
  rw [dist_eq_norm] at hz hz1 ha ha1 hb hb1
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right a b c] at hab
  have hza : dist z a = ‖(z - c) - (a - c)‖ := by
    rw [dist_eq_norm, sub_sub_sub_cancel_right]
  have hzb : dist z b = ‖(z - c) - (b - c)‖ := by
    rw [dist_eq_norm, sub_sub_sub_cancel_right]
  rw [hza] at heq ⊢
  rw [hzb] at heq
  set Z := z - c
  set A := a - c
  set B := b - c
  clear_value Z A B
  have hS : ‖A + B‖ ^ 2 < ρ ^ 2 := by
    have e1 := norm_add_sq_real A B
    have e2 := norm_sub_sq_real A B
    nlinarith
  have hSρ : ‖A + B‖ < ρ := by nlinarith [norm_nonneg (A + B)]
  have hZρ : ‖Z‖ ≤ ρ := by nlinarith [norm_nonneg Z]
  have hin : |⟪Z, A + B⟫| < ρ ^ 2 := by
    refine (abs_real_inner_le_norm Z (A + B)).trans_lt ?_
    calc ‖Z‖ * ‖A + B‖ ≤ ρ * ‖A + B‖ := mul_le_mul_of_nonneg_right hZρ (norm_nonneg _)
      _ < ρ * ρ := mul_lt_mul_of_pos_left hSρ hρ
      _ = ρ ^ 2 := by ring
  have h2 : 2 * ‖Z - A‖ ^ 2 = 2 * ‖Z‖ ^ 2 + ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * ⟪Z, A + B⟫ := by
    have e1 := norm_sub_sq_real Z A
    have e2 := norm_sub_sq_real Z B
    rw [inner_add_right]
    have e3 : ‖Z - A‖ ^ 2 = ‖Z - B‖ ^ 2 := by rw [heq]
    linarith
  obtain ⟨hl, hu⟩ := abs_lt.mp hin
  constructor <;> nlinarith

end
