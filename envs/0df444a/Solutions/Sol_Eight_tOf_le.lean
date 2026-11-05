-- Prove2me | solution 1 for Eight.tOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:41:37.828683+00:00
-- url     : https://prove2.me/submissions/bc287152-c145-4075-907d-f93cc3062318

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_App_Pieces

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {lam : ℕ} (hl : 1 ≤ lam) : tOf lam ≤ lam := by
  unfold tOf
  omega
end Eight
