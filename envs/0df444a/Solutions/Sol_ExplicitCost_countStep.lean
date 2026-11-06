-- Prove2me | solution 1 for ExplicitCost.countStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:04.122131+00:00
-- url     : https://prove2.me/submissions/7ba70e14-e7f5-4cee-92b7-d8a5d205260b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Count
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountStep
import Theorems.Thm_ExplicitCost_countStepFrom
import Theorems.Thm_ExplicitCost_boundBelow
import Theorems.Thm_ExplicitCost_chainLabel
import Theorems.Thm_ExplicitCost_partAPrinted


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines
namespace ExplicitCost
theorem _root_.solution : CountStep := countStepFrom chainLabel boundBelow partAPrinted
end ExplicitCost
