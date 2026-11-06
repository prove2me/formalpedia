-- Prove2me | solution 1 for CircuitLowerBound.Tab.table_dq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:32:00.582983+00:00
-- url     : https://prove2.me/submissions/33430d16-f1ab-43cb-81e3-fdeece3eaa7d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
import Theorems.Thm_CircuitLowerBound_Tab_forall_fam
import Theorems.Thm_CircuitLowerBound_Tab_forall_flatten
import Theorems.Thm_CircuitLowerBound_Tab_one_le_dep
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}
variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
variable {N}
namespace CircuitLowerBound.Tab
theorem _root_.solution : ∀ c ∈ table N, c.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.2.2.2.2.1 ≤ 2 * dep N := by
  classical
  have hd := one_le_dep N
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, forall_fam]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_6 => intro p; have := p.2.2.isLt; simp only [c2]; omega
  case refine_10 => intro p; have := p.2.2.isLt; split_ifs <;> simp only [c2, taut] <;> omega
  case refine_11 => intro p; have := p.2.isLt; omega
  case refine_12 => intro p; have := p.2.isLt; omega
  all_goals (intros; (try split_ifs) <;> (try simp only [c1, c2, taut]) <;> omega)
end CircuitLowerBound.Tab
