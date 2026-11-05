-- Prove2me | solution 1 for Eight.Width.splitAll_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:09.752922+00:00
-- url     : https://prove2.me/submissions/32482eae-3630-493b-8259-0073693e713e

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
theorem _root_.solution (ys : List V) (C : List (V × Bool)) (φ : List (List (V × Bool))) :
    splitAll ys (C :: φ) = splitClause (ys.take (C.length - 3)) C ++ splitAll (ys.drop (C.length - 3)) φ := rfl
end Eight.Width
