-- Prove2me | solution 1 for Eight.Level.firstLevel_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:59.175071+00:00
-- url     : https://prove2.me/submissions/7d96079a-4e06-461e-b4b7-65b91c52d479

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_Level_SecPseudocode

set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Paper
namespace Eight.Level
theorem _root_.solution {δ' : ℝ} (hδ' : 0 < δ') : 72 / δ' ≤ levelK (firstLevel hδ') ∧ Eight.Level.levelE (firstLevel hδ') ≤ δ' / 12 := by
  classical
  exact Nat.find_spec (exists_first hδ')
end Eight.Level
