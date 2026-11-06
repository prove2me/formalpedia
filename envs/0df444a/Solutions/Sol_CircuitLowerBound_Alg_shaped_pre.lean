-- Prove2me | solution 1 for CircuitLowerBound.Alg.shaped_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:08.942107+00:00
-- url     : https://prove2.me/submissions/96e06bf3-8815-4257-80e1-038534267628

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_CircuitLowerBound_Alg_pre_cases
import Theorems.Thm_CircuitLowerBound_Alg_shaped_nil
import Theorems.Thm_CircuitLowerBound_Alg_shaped_false
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}
namespace CircuitLowerBound.Alg
theorem _root_.solution (hF : FormOK a₀ g F) (x : List Bool) : Shaped3 (pre F fb x).1.length (pre F fb x).2 := by
  rcases pre_cases F fb x with ⟨_, h2, h3, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, e⟩ <;> rw [e]
  · exact (hF _ _ _ _ h2 h3).1
  · exact shaped_nil
  · exact shaped_false
  · exact shaped_nil
  · exact shaped_false
  · exact shaped_false
end CircuitLowerBound.Alg
