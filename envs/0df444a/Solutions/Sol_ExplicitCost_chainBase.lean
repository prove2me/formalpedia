-- Prove2me | solution 1 for ExplicitCost.chainBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:54.402218+00:00
-- url     : https://prove2.me/submissions/c6f4d9a3-4b62-41b0-86b9-d5b246f7b5d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain
import Theorems.Thm_ExplicitCost_chainBaseFrom
import Theorems.Thm_ExplicitCost_chainLabel
import Theorems.Thm_ExplicitCost_crudeBounds


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution : ChainBase := chainBaseFrom chainLabel crudeBounds
end ExplicitCost
