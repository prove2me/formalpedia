-- Prove2me | solution 1 for CongruenceSubgroup.two_mul_index_gamma1_sup_zpowers_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d8f18da2-d338-5323-ac6f-7aed33356ac6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one

set_option autoImplicit false

open scoped MatrixGroups

namespace CuspKit

theorem neg_one_not_mem_gamma1 (N : ℕ) [NeZero N] (hN : 3 ≤ N) : (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have h00 := h.1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq, Int.cast_neg, Int.cast_one] at h00

  have h2 : ((2 : ℕ) : ZMod N) = 0 := by
    have : (1 : ZMod N) + 1 = 0 := by
      nth_rewrite 1 [← h00]; exact neg_add_cancel 1
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem mem_zpowers_neg_one {z : SL(2, ℤ)} (hz : z ∈ Subgroup.zpowers (-1 : SL(2, ℤ))) : z = 1 ∨ z = -1 := by
  rw [Subgroup.zpowers_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx => right; simpa using hx
  | one => left; rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · left; exact one_mul 1
    · right; exact one_mul _
    · right; exact mul_one _
    · left; rw [neg_mul_neg, one_mul]
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · left; exact inv_one
    · right; exact inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, one_mul])

scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rcases mem_zpowers_neg_one hn with rfl | rfl
  · rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  · rw [mul_neg, mul_one, neg_mul, mul_inv_cancel]; exact Subgroup.mem_zpowers _

end CuspKit
p2m_reactivate "P2MW.S_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one.CuspKit"

open CuspKit in
theorem solution
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    2 * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index = (CongruenceSubgroup.Gamma1 N).index := by
  set H := CongruenceSubgroup.Gamma1 N
  set Z := Subgroup.zpowers (-1 : SL(2, ℤ))
  have hneg : (-1 : SL(2, ℤ)) ∉ H := neg_one_not_mem_gamma1 N hN
  have hrel : H.relIndex (H ⊔ Z) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), fun b hb => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rcases mem_zpowers_neg_one hz with rfl | rfl
    ·
      rw [mul_one, xor_def]
      right
      refine ⟨hy, fun h => hneg ?_⟩
      have : y⁻¹ * (y * -1) ∈ H := H.mul_mem (H.inv_mem hy) h
      rwa [inv_mul_cancel_left] at this
    ·
      rw [xor_def]
      left
      refine ⟨by rw [mul_assoc, neg_mul_neg, one_mul, mul_one]; exact hy, fun h => hneg ?_⟩
      have : y⁻¹ * (y * -1) ∈ H := H.mul_mem (H.inv_mem hy) h
      rwa [inv_mul_cancel_left] at this
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ Z), hrel]

end S_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one
end P2MW
export P2MW.S_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one (solution)
