-- Prove2me | solution 1 for ClauseBound.Boson.mem_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:49.40524+00:00
-- url     : https://prove2.me/submissions/7499b51d-c589-432f-8266-5d9b19242d93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic
namespace ClauseBound.Boson
theorem _root_.solution {m : ℕ} {τ : Multiset ℕ} : τ ∈ P m ↔ τ.sum = m ∧ 0 ∉ τ := by
  unfold P
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact ⟨q.parts_sum, fun h => lt_irrefl 0 (q.parts_pos h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨τ, fun {i} hi => Nat.pos_of_ne_zero fun h0 => h2 (h0 ▸ hi), h1⟩, Finset.mem_univ _, rfl⟩
end ClauseBound.Boson
