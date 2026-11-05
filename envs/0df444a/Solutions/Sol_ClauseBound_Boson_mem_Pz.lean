-- Prove2me | solution 1 for ClauseBound.Boson.mem_Pz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:01.452268+00:00
-- url     : https://prove2.me/submissions/542c876f-899e-48bb-9b02-7fdfea7c1ff8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic
import Theorems.Thm_ClauseBound_Boson_mem_P

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic
namespace ClauseBound.Boson
theorem _root_.solution {m : ℤ} {τ : Multiset ℕ} : τ ∈ Pz m ↔ (τ.sum : ℤ) = m ∧ 0 ∉ τ := by
  unfold Pz
  split_ifs with h
  · rw [mem_P]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  · constructor
    · intro h0
      simp at h0
    · rintro ⟨h1, -⟩
      omega
end ClauseBound.Boson
