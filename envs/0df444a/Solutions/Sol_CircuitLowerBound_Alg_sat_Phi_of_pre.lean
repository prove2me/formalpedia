-- Prove2me | solution 1 for CircuitLowerBound.Alg.sat_Phi_of_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:09.979433+00:00
-- url     : https://prove2.me/submissions/48176ddf-f00c-4ab0-a04a-2e232d358314

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Theorems.Thm_CircuitLowerBound_Alg_pre_cases
import Theorems.Thm_CircuitLowerBound_Alg_sat_nil

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}
namespace CircuitLowerBound.Alg
theorem _root_.solution (hF : FormOK a₀ g F) (hb : FlipOK fb) (x : List Bool) (h : ¬Sat (pre F fb x).2) : Sat (Phi (ones x)) := by
  rcases pre_cases F fb x with ⟨h1, h2, h3, e⟩ | ⟨_, _, _, e⟩ | ⟨h1, h2, _⟩ | ⟨_, _, e⟩ | ⟨h1, h2, _⟩ | ⟨h1, _⟩
  · rw [e, (hF _ _ _ _ h2 h3).2.2, not_not] at h
    unfold Phi
    rw [if_pos h1, if_pos h2]
    exact ⟨fun i => eval (toC (decC (rest x))) (toWord (ones x) i), h⟩
  · rw [e] at h
    exact absurd sat_nil h
  · unfold Phi
    rw [if_pos h1, if_neg h2]
    exact sat_nil
  · rw [e] at h
    exact absurd sat_nil h
  · unfold Phi
    rw [if_neg (by omega), if_pos h1, if_neg fun h3 => by rw [(hb _ h1).2 h3] at h2; exact Bool.noConfusion h2]
    exact sat_nil
  · unfold Phi
    rw [if_neg (by omega), if_neg (by omega)]
    exact sat_nil
end CircuitLowerBound.Alg
