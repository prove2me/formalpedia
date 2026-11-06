-- Prove2me | solution 1 for CircuitLowerBound.Oracle.liftCfg_init
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:52:01.125199+00:00
-- url     : https://prove2.me/submissions/0fe5e75c-ee91-4797-94a2-0e6e8769f9e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Theorems.Thm_CircuitLowerBound_Oracle_initList_stk
import Theorems.Thm_Groundwork_TM_Run_one


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)
namespace CircuitLowerBound.Oracle
theorem _root_.solution (n : NS → List Bool) (s : List (M.tm.Γ M.tm.k₀)) :
    liftCfg n (initList M.tm s) = ⟨some (.inl M.tm.main), (M.tm.initialState, none), stk M (one M.tm.k₀ s) n⟩ := by
  unfold liftCfg
  rw [initList_stk]
  rfl
end CircuitLowerBound.Oracle
