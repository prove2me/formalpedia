-- Prove2me | solution 1 for Eight.Width.widthReduce_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:59.43201+00:00
-- url     : https://prove2.me/submissions/ef02e43d-424a-4031-93df-cc5e70216a77

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
theorem _root_.solution (φ : CNF n) : widthReduce φ = (splitAll (freshFin n (numFresh φ)) (lift (numFresh φ) φ)).dedup := rfl
end Eight.Width
