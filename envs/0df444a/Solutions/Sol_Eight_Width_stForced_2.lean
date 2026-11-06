-- Prove2me | solution 2 for Eight.Width.stForced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:07.7162+00:00
-- url     : https://prove2.me/submissions/be658ced-fed9-4f4e-881d-c9d3a07f9e03

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_holds_forced

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution : StForced := fun _ a y l₁ l₂ => ⟨holds_forced a y l₁ l₂, by simp [forced]⟩
end Eight.Width
