-- Prove2me | solution 1 for CircuitLowerBound.Oracle.run_protocol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:25.963868+00:00
-- url     : https://prove2.me/submissions/6d7b20c3-6f27-46cd-9c47-73c280bb5112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Theorems.Thm_CircuitLowerBound_Oracle_run_round
import Theorems.Thm_CircuitLowerBound_Oracle_run_finish
import Theorems.Thm_CircuitLowerBound_Oracle_run_query
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)
namespace CircuitLowerBound.Oracle
theorem _root_.solution {T : ℕ} {x : List Bool} {b : Bool} {ans : List Bool} {r : ℕ} (h : Protocol M T x b ans r) :
    ∃ t ≤ (r + 1) * (3 * (ans.length + r) + 3 * x.length + T + 12),
      Run (stp M SAT) ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ t
        ⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ := by
  induction h with
  | @done ans r hR =>
    obtain ⟨t, ht, r1⟩ := run_round SAT hR
    refine ⟨_, ?_, r1.trans (run_finish SAT x ans b)⟩
    have : 1 * (3 * (ans.length + r) + 3 * x.length + T + 12) ≤ (r + 1) * (3 * (ans.length + r) + 3 * x.length + T + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  | @query ans w r hR _ ih =>
    obtain ⟨t, ht, r1⟩ := run_round SAT hR
    obtain ⟨t', ht', r3⟩ := ih
    refine ⟨_, ?_, (r1.trans (run_query SAT x ans w)).trans r3⟩
    rw [List.length_append, List.length_singleton] at ht'
    have e : ans.length + 1 + r = ans.length + (r + 1) := by ring
    rw [e] at ht'
    have : (r + 1 + 1) * (3 * (ans.length + (r + 1)) + 3 * x.length + T + 12)
        = (r + 1) * (3 * (ans.length + (r + 1)) + 3 * x.length + T + 12) + (3 * (ans.length + (r + 1)) + 3 * x.length + T + 12) := by ring
    omega
end CircuitLowerBound.Oracle
