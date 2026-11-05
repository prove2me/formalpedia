-- Prove2me | solution 1 for ClauseBound.Grid.abs_boole_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:15:36.348014+00:00
-- url     : https://prove2.me/submissions/b5434a1b-9c68-4914-9bea-5c4797175f5e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution (q : Prop) [Decidable q] : |if q then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp
end ClauseBound.Grid
