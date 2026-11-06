-- Prove2me | solution 1 for Eight.Width.lift_fresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:00:11.003729+00:00
-- url     : https://prove2.me/submissions/8e573cb2-fffa-407c-813b-5db823411bd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_castAdd_notMem_freshFin

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution (N : ℕ) (φ : CNF n) : ∀ C ∈ lift N φ, ∀ l ∈ C, l.1 ∉ freshFin n N := by
  intro C hC l hl
  simp only [lift, List.mem_map] at hC
  obtain ⟨C', _, rfl⟩ := hC
  obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
  exact castAdd_notMem_freshFin n N l'.1
end Eight.Width
