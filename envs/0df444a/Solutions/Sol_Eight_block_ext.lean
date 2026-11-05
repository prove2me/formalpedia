-- Prove2me | solution 1 for Eight.block_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:06.542349+00:00
-- url     : https://prove2.me/submissions/0f2a54c4-a3d0-4cba-834c-992368cb9aef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {p q : Block} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) (h3 : p.2.2 = q.2.2) : p = q := Prod.ext h1 (Prod.ext h2 h3)
end Eight
