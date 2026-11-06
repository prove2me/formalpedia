-- Prove2me | solution 1 for ExplicitCost.totalRoom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:23:40.471001+00:00
-- url     : https://prove2.me/submissions/74eb441b-6dd0-4430-b2f7-70e83c92ed9c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_TotalRoom
import Theorems.Thm_ExplicitCost_totalRoomFrom
import Theorems.Thm_ExplicitCost_chainBase
import Theorems.Thm_ExplicitCost_chainLevels


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines Finset
namespace ExplicitCost
theorem _root_.solution : TotalRoom := totalRoomFrom chainBase chainLevels
end ExplicitCost
