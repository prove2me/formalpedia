-- Prove2me | solution 1 for ExplicitCost.totalCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:05.067566+00:00
-- url     : https://prove2.me/submissions/dde1084a-7fab-4898-ade9-6dd8b539d413

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CountBase
import Definitions.Def_CountedRecursion_CountStep
import Definitions.Def_Tower_Cost
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_TotalCount
import Theorems.Thm_ExplicitCost_totalCountFrom
import Theorems.Thm_ExplicitCost_countBase
import Theorems.Thm_ExplicitCost_countStep
import Theorems.Thm_ExplicitCost_exponentFits
import Theorems.Thm_QueryMachines_Tower_costShape


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines
namespace ExplicitCost
theorem _root_.solution : TotalCount := totalCountFrom countBase countStep exponentFits Tower.costShape
end ExplicitCost
