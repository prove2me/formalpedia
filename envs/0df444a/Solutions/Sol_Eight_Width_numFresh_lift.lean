-- Prove2me | solution 1 for Eight.Width.numFresh_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:28:00.621524+00:00
-- url     : https://prove2.me/submissions/47ae8b36-1ecf-43b0-ad8b-3666bec18cde

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
theorem _root_.solution (N : ℕ) (φ : CNF n) : numFresh (lift N φ) = numFresh φ := by
  simp [numFresh, lift, Function.comp_def]
end Eight.Width
