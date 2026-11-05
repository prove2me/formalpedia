-- Prove2me | solution 1 for Eight.Width.numFresh_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:10.699941+00:00
-- url     : https://prove2.me/submissions/c1b400ae-29d9-4261-9e31-59e0bc97c90e

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
namespace Eight.Width
theorem _root_.solution (C : List (V × Bool)) (φ : List (List (V × Bool))) :
    numFresh (C :: φ) = (C.length - 3) + numFresh φ := by simp [numFresh]
end Eight.Width
