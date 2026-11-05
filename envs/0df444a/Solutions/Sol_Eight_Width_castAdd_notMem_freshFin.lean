-- Prove2me | solution 1 for Eight.Width.castAdd_notMem_freshFin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:29:00.277195+00:00
-- url     : https://prove2.me/submissions/ce9bd751-fe9e-4ea5-a78a-bc43b74be93e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution (n N : ℕ) (i : Fin n) : Fin.castAdd N i ∉ freshFin n N := by
  simp only [freshFin, List.mem_map, not_exists, not_and]
  intro j _ e
  have := congrArg Fin.val e
  simp at this
  omega
end Eight.Width
