-- Prove2me | solution 1 for ClauseBound.Part.Lower.sum_v_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:33:57.805714+00:00
-- url     : https://prove2.me/submissions/80f7a28f-509d-4dc4-b8ff-0d562cc02224

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_T1_ge
import Theorems.Thm_ClauseBound_Part_Lower_T3_le
import Theorems.Thm_ClauseBound_Part_Lower_one_sub_exp_neg_ge

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {y η : ℝ} (hy : 0 < y) (hy2 : y ≤ 2) (hη : 0 ≤ η) (n : ℕ) (hn : 1 ≤ η * (n : ℝ) ^ 2) :
    1 / y ^ 2 - 1 / 4 - 486 * η / y ^ 4 ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(y * v)) * (1 - η * (v : ℝ) ^ 2) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Real.exp (-y) := ⟨_, rfl⟩
  have r0 : 0 < r := hr ▸ Real.exp_pos _
  have r1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg r0.le]
  have e (v : ℕ) : Real.exp (-(y * v)) = r ^ v := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; ring
  have hG : HasSum (fun v : ℕ => (v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) (r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).sub ((summable_pow_mul_geometric_of_norm_lt_one 3 hnorm).hasSum.mul_left η)
  have hle : r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ ∑ v ∈ Icc 1 n, ((v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) := by
    have h := sum_le_hasSum (Icc 1 n) (fun v hv => ?_) hG.neg
    · rw [Finset.sum_neg_distrib] at h
      linarith
    · have e2 : -((v : ℝ) * r ^ v - η * ((v : ℝ) ^ 3 * r ^ v)) = (v : ℝ) * r ^ v * (η * (v : ℝ) ^ 2 - 1) := by ring
      rw [e2]
      rcases Nat.eq_zero_or_pos v with rfl | hv0
      · simp
      · have hvn : n < v := by
          by_contra hcon
          exact hv (Finset.mem_Icc.2 ⟨hv0, not_lt.1 hcon⟩)
        have hvn' : (n : ℝ) ≤ v := by exact_mod_cast hvn.le
        have h2 : η * (n : ℝ) ^ 2 ≤ η * (v : ℝ) ^ 2 := by gcongr
        exact mul_nonneg (by positivity) (by linarith)
  have h3 : ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 486 / y ^ 4 := by
    have h4 : y / 3 ≤ 1 - r := hr ▸ one_sub_exp_neg_ge hy.le hy2
    calc _ ≤ 6 / (1 - r) ^ 4 := T3_le r0.le r1
      _ ≤ 6 / (y / 3) ^ 4 := by gcongr
      _ = 486 / y ^ 4 := by field_simp; norm_num
  have h5 : 1 / y ^ 2 - 1 / 4 ≤ r / (1 - r) ^ 2 := hr ▸ T1_ge hy
  have h6 : η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 486 * η / y ^ 4 := by
    calc _ ≤ η * (486 / y ^ 4) := by gcongr
      _ = _ := by ring
  calc _ ≤ r / (1 - r) ^ 2 - η * ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v := by linarith
    _ ≤ _ := hle
    _ = _ := Finset.sum_congr rfl fun v _ => by rw [e]; ring
end ClauseBound.Part.Lower
