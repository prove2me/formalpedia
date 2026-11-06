-- Prove2me | solution 1 for ExplicitCost.labelLengthIsL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:18.713347+00:00
-- url     : https://prove2.me/submissions/f9eff159-8476-4796-aa2d-8a86b75ee039

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingNumbers
import Theorems.Thm_ExplicitCost_labelLength_groupingInput
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
variable {P B}
private theorem ceil_div_nat (n d : ℕ) (hd : 0 < d) : ⌈(n : ℝ) / d⌉₊ = (n + d - 1) / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈(n : ℝ) / d⌉₊ := ⟨_, rfl⟩
  rw [← hq]
  apply le_antisymm
  · rw [hq, Nat.ceil_le, div_le_iff₀ hdr]
    have h := Nat.div_add_mod (n + d - 1) d
    have h' := Nat.mod_lt (n + d - 1) hd
    have h2 : n ≤ d * ((n + d - 1) / d) := by omega
    calc (n : ℝ) ≤ ((d * ((n + d - 1) / d) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = _ := by rw [Nat.cast_mul, mul_comm]
  · have h1 : (n : ℝ) / d ≤ q := hq ▸ Nat.le_ceil _
    rw [div_le_iff₀ hdr] at h1
    have h2 : n ≤ q * d := by exact_mod_cast h1
    exact Nat.lt_succ_iff.1 (Nat.div_lt_of_lt_mul (calc n + d - 1 < q * d + d := by omega
      _ = d * (q + 1) := by ring))
end ExplicitCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
variable {P B}
namespace ExplicitCost
theorem _root_.solution : LabelLengthIsL := by
  intro a b K g N P B hb hab hK hN
  refine ⟨?_, ?_⟩
  · have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    have hd : 0 < b * K ^ 2 := by positivity
    have e : ((N.U : ℝ) + 2 * ((a : ℝ) / b) * g * P) / (K : ℝ) ^ 2 = ((b * N.U + 2 * a * g * P : ℕ) : ℝ) / ((b * K ^ 2 : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [labelLength_groupingInput a b K N hN, min_eq_left hab, AppRunningTime.Lof, e, ceil_div_nat _ _ hd]
  · unfold bitsOut AppRunningTime.B'of
    have h : 2 * g * P + K - 1 = 2 * (g * P) + (K - 1) := by
      have := Nat.mul_assoc 2 g P
      omega
    rw [h]
end ExplicitCost
