-- Prove2me | solution 1 for Exits.stCountCostOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:28.092586+00:00
-- url     : https://prove2.me/submissions/5aaa0535-cc04-456a-b1fc-9362cebc67fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Exits_Level
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Count
import Theorems.Thm_Exits_COUNT_polyTimeSteps
import Theorems.Thm_Eight_ViaGrouping_count_cost_of
import Theorems.Thm_Eight_numSat_nil
import Theorems.Thm_Exits_two_le_levelK
import Theorems.Thm_Exits_zero_lt_levelG
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list



set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping
namespace Exits
theorem _root_.solution : StCountCostOf := by
  intro hL hKp hC δ' ℓ hδ' h1 hK hE
  refine ⟨COUNT_polyTimeSteps hKp hC ℓ, ?_⟩
  obtain ⟨A₀, hA₀⟩ := ViaGrouping.count_cost_of hδ' h1 (zero_lt_levelG ℓ) hK
    (hL (levelK ℓ) (δ' / 12) (CLIQUE ℓ) (two_le_levelK ℓ) (by positivity) ((hC ℓ).2.mono hE))
  have hA : (A₀ : ℝ) ≤ ((A₀ + 5 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right A₀ 5
  refine ⟨A₀ + 5, fun Φ hΦ => ?_⟩
  cases hemp : Φ.isEmpty with
  | true =>
    -- «if m = 0 then return 1»
    obtain rfl : Φ = [] := List.isEmpty_iff.1 hemp
    have s0 : size ([] : Formula) = 1 := rfl
    have s1 : size (1 : ℤ) ≤ 2 := by
      rw [size_int]
      exact Nat.succ_le_succ (Nat.size_le.2 (by norm_num))
    have h5 : (1 : ℝ) ≤ ((A₀ + 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ A₀ + 5)
    refine ⟨1, ?_, ?_⟩
    · rw [numSat_nil, Nat.cast_one]
      refine (ite_runs_true rfl (const_runs (1 : ℤ) ([] : Formula))).mono le_rfl ?_
      rw [s0, one_pow, mul_one]
      omega
    · rw [List.length_nil, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one, Nat.cast_one]
      exact h5
  | false =>
    -- «let m ≥ 1»: line 8
    obtain ⟨T, hrun, hT⟩ := hA₀ Φ hΦ
    have hs1 : 1 ≤ size Φ := by rw [size_list]; omega
    have h2 : size Φ ^ A₀ ≤ size Φ ^ (A₀ + 5) := Nat.pow_le_pow_right hs1 (by omega)
    have h3 : 1 ≤ size Φ ^ (A₀ + 5) := Nat.one_le_pow _ _ hs1
    refine ⟨T, (ite_runs_false hemp hrun).mono le_rfl ?_, hT.trans (mul_le_mul_of_nonneg_right hA (by positivity))⟩
    calc A₀ * size Φ ^ A₀ + 1 ≤ A₀ * size Φ ^ (A₀ + 5) + 5 * size Φ ^ (A₀ + 5) := Nat.add_le_add (Nat.mul_le_mul_left _ h2) (by omega)
      _ = (A₀ + 5) * size Φ ^ (A₀ + 5) := (Nat.add_mul _ _ _).symm
end Exits
