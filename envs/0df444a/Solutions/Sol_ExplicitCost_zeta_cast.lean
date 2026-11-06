-- Prove2me | solution 1 for ExplicitCost.zeta_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:24:10.767541+00:00
-- url     : https://prove2.me/submissions/1b623040-e458-40ee-a9b3-7f8620666296

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (l : ℕ) : (1 : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ) = Levels.Gen.zeta l := by
  unfold Levels.Gen.zeta
  push_cast
  rfl
end ExplicitCost
