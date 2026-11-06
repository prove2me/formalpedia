-- Prove2me | solution 1 for ExplicitCost.roomIsWithinTheBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:05.233027+00:00
-- url     : https://prove2.me/submissions/ea49d640-7d15-41b5-8955-c85157369a14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RoomWithin
import Theorems.Thm_ExplicitCost_roomIsWithinTheBoundFrom
import Theorems.Thm_ExplicitCost_boundBelow
import Theorems.Thm_ExplicitCost_chainLabel
import Theorems.Thm_ExplicitCost_chainLevels
import Theorems.Thm_ExplicitCost_exponentFits
import Theorems.Thm_ExplicitCost_partAPrinted


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed Finset
namespace ExplicitCost
theorem _root_.solution : RoomIsWithinTheBound := roomIsWithinTheBoundFrom chainLabel boundBelow chainLevels exponentFits partAPrinted
end ExplicitCost
