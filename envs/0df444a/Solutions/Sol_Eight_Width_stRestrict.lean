-- Prove2me | solution 1 for Eight.Width.stRestrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:05:08.004169+00:00
-- url     : https://prove2.me/submissions/6061e907-cf12-447e-830b-4f2d9a56141f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_splitAll_sound
import Theorems.Thm_Eight_Width_holds_dedup
import Theorems.Thm_Eight_Width_holds_lift

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution : StRestrict := fun _ φ b h =>
  (holds_lift _ φ b).1 (splitAll_sound b _ _ (holds_dedup.1 h))
end Eight.Width
