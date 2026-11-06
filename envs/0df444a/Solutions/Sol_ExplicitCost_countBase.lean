-- Prove2me | solution 1 for ExplicitCost.countBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:38.339877+00:00
-- url     : https://prove2.me/submissions/07fbf657-c5ca-499b-b75b-70c59e36eb26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountBase
import Theorems.Thm_ExplicitCost_countBaseFrom
import Theorems.Thm_ExplicitCost_chainLabel


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution : CountBase := countBaseFrom chainLabel
end ExplicitCost
