-- Prove2me | solution 1 for ExplicitCost.chainExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:14.613508+00:00
-- url     : https://prove2.me/submissions/68de1169-3756-43f1-b934-f29d70c001ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain
import Theorems.Thm_ExplicitCost_chainExponentFrom
import Theorems.Thm_ExplicitCost_chainLabel
import Theorems.Thm_ExplicitCost_partAPrinted


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution : ChainExponent := chainExponentFrom chainLabel partAPrinted
end ExplicitCost
