-- Prove2me | solution 1 for CircuitLowerBound.Clause.wfa_litG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:51:31.553559+00:00
-- url     : https://prove2.me/submissions/dcd36473-66d7-40b7-8455-69cf73ccbbfd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_length_timeG
import Theorems.Thm_CircuitLowerBound_Clause_wfa_timeG
import Theorems.Thm_CircuitLowerBound_Clause_wfa_posG
import Theorems.Thm_CircuitLowerBound_Clause_Fw_lt
import Theorems.Thm_CircuitLowerBound_Clause_offA_ge
import Theorems.Thm_CircuitLowerBound_Clause_dWire_lt
import Theorems.Thm_CircuitLowerBound_Blocks_wfa_append


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R kbm Dq P : ℕ) {ι : ℕ} (hι : ι < 3) :
    WFa (offA n bq bt rb R (5 + kbm + Dq) ι) (litG n bq bt rb R kbm Dq P ι) := by
  have hg := offA_ge n bq bt rb R (5 + kbm + Dq) ι
  have f0 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 0) hι (by omega)
  have f1 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 1) hι (by omega)
  have f2 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 2) hι (by omega)
  have f3 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 3) hι (by omega)
  rw [litG, wfa_append, length_timeG]
  refine ⟨wfa_timeG (by omega) (by omega) (by omega), ?_⟩
  rw [show offA n bq bt rb R (5 + kbm + Dq) ι + (3 * bt + 4) = offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt by omega]
  exact wfa_posG (by omega) (by omega) (by omega) (by omega) fun i => by have := dWire_lt n rb R kbm Dq hι i; omega
end CircuitLowerBound.Clause
