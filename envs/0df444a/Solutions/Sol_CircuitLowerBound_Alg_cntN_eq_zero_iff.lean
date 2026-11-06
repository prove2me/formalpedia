-- Prove2me | solution 1 for CircuitLowerBound.Alg.cntN_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:49:30.413089+00:00
-- url     : https://prove2.me/submissions/f622172a-0482-4187-bd2b-414f06e0d4a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_PaddedDescent_Host
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Machine

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing Parse
open CircuitLowerBound.Alg
variable {F : (MCode × List Unit × ℕ) × List GateD → List Unit × Cnf} {fb : List Unit → Bool}
variable {a₀ : ℕ} {g : MCode → ℕ}
namespace CircuitLowerBound.Alg
theorem _root_.solution {N : ℕ} {ψ : Cnf} (h : ∀ D ∈ ψ, ∀ l ∈ D, l.1 < N) : CountKSat.cntN N ψ = 0 ↔ ¬Sat ψ := by
  unfold CountKSat.cntN
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h1 ⟨a, ha⟩
    refine h1 (Finset.mem_univ fun i : Fin N => a i) fun D hD => ?_
    obtain ⟨l, hl, h2⟩ := ha D hD
    exact ⟨l, hl, by rw [CountKSat.ext, dif_pos (h D hD l hl)]; exact h2⟩
  · intro h1 a _ h2
    exact h1 ⟨CountKSat.ext a, h2⟩
end CircuitLowerBound.Alg
