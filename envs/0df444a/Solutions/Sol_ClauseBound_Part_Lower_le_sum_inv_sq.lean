-- Prove2me | solution 1 for ClauseBound.Part.Lower.le_sum_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:32:36.745092+00:00
-- url     : https://prove2.me/submissions/89cb9e07-585d-49a3-a3b8-a3dcaf66c594

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
theorem _root_.solution {K : ℕ} (hK : 1 ≤ K) : Real.pi ^ 2 / 6 - 1 / K ≤ ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 := by
  have h : Real.pi ^ 2 / 6 ≤ ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 + 1 / K := by
    rw [← hasSum_zeta_two.tsum_eq]
    refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun M => ?_
    have h1 : range M ⊆ insert 0 (Ioc 0 (max K M)) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | h0
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_Ioc.2 ⟨h0, (Finset.mem_range.1 hi).le.trans (le_max_right _ _)⟩)
    have h2 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := K) (n := max K M) (by omega) (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ ((max K M : ℕ) : ℝ)⁻¹ := by positivity
    calc ∑ i ∈ range M, 1 / (i : ℝ) ^ 2 ≤ ∑ i ∈ insert 0 (Ioc 0 (max K M)), 1 / (i : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg h1 fun _ _ _ => by positivity
      _ = ∑ i ∈ Ioc 0 (max K M), 1 / (i : ℝ) ^ 2 := by rw [Finset.sum_insert (by simp)]; simp
      _ = ∑ i ∈ Ioc 0 K, 1 / (i : ℝ) ^ 2 + ∑ i ∈ Ioc K (max K M), 1 / (i : ℝ) ^ 2 :=
          (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (le_max_left _ _)).symm
      _ ≤ _ := by
          simp only [one_div] at h2 ⊢
          linarith
  linarith
end ClauseBound.Part.Lower
