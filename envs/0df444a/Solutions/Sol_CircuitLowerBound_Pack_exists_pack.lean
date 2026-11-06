-- Prove2me | solution 1 for CircuitLowerBound.Pack.exists_pack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:17.050431+00:00
-- url     : https://prove2.me/submissions/33240f17-d15a-4d0b-9f32-7c181f9705da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
variable {e : MCode} {L P : ℕ}
namespace CircuitLowerBound.Pack
theorem _root_.solution (e : MCode) (L : ℕ) (j : ℕ) : ∃ r t q, t < 2 ^ bt e L ∧ q < 2 ^ bq e L ∧ j = (r * 2 ^ bt e L + t) * 2 ^ bq e L + q :=
  ⟨j / 2 ^ bq e L / 2 ^ bt e L, j / 2 ^ bq e L % 2 ^ bt e L, j % 2 ^ bq e L, Nat.mod_lt _ (by positivity), Nat.mod_lt _ (by positivity), by
    rw [Nat.div_add_mod', Nat.div_add_mod']⟩
end CircuitLowerBound.Pack
