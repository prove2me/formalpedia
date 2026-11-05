-- Prove2me | solution 1 for ClauseBound.Boson.Text.mem_win
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:27.662203+00:00
-- url     : https://prove2.me/submissions/a825e0fa-57c1-4065-8339-0891b5a4e8fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Text

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset MvPolynomial
open ClauseBound.Boson.Text
namespace ClauseBound.Boson.Text
theorem _root_.solution {M : ℕ} {k : ℤ} : k ∈ win M ↔ k ≠ 0 ∧ -(M : ℤ) ≤ k ∧ k ≤ M := by
  simp only [win, mem_union, mem_image, mem_Icc]
  constructor
  · rintro (⟨l, ⟨h1, h2⟩, rfl⟩ | ⟨l, ⟨h1, h2⟩, rfl⟩) <;> omega
  · rintro ⟨h0, h1, h2⟩
    rcases lt_or_gt_of_ne h0 with h | h
    · exact Or.inl ⟨(-k).toNat, by omega, by omega⟩
    · exact Or.inr ⟨k.toNat, by omega, by omega⟩
end ClauseBound.Boson.Text
