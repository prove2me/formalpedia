-- Prove2me | solution 1 for CircuitLowerBound.TabF.sat_iff_testBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:33:52.423979+00:00
-- url     : https://prove2.me/submissions/7056b18b-e2f7-4c14-be5e-fe33f80eebef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution (φ : Cnf) (M : ℕ) (hv : ∀ C ∈ φ, ∀ l ∈ C, l.1 < M) :
    Sat φ ↔ ∃ α < 2 ^ M, ∀ C ∈ φ, ∃ l ∈ C, α.testBit l.1 = l.2 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Nat.ofBits fun i : Fin M => f i, Nat.ofBits_lt_two_pow _, fun C hC => ?_⟩
    obtain ⟨l, hl, h⟩ := hf C hC
    exact ⟨l, hl, by rw [Nat.testBit_ofBits_lt _ _ (hv C hC l hl)]; exact h⟩
  · rintro ⟨α, -, h⟩
    exact ⟨fun i => α.testBit i, h⟩
end CircuitLowerBound.TabF
