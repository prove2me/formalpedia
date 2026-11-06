-- Prove2me | solution 1 for ExplicitCost.crudeBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:44.336998+00:00
-- url     : https://prove2.me/submissions/a458fe51-5a99-4831-9fb4-84e2f42bf53a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CrudeBounds
import Theorems.Thm_ExplicitCost_crude_plain
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_K_le_g
import Theorems.Thm_ClauseBound_Gen_Rate_big_le_K


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : CrudeBounds := by
  intro c x₀ l lam B L hx hlam hB hL
  have hK := ClauseBound.Gen.Rate.big_le_K hx l
  exact crude_plain c _ _ lam B L (by omega) (ClauseBound.Gen.Rate.K_le_g x₀ l) hlam hB hL
end ExplicitCost
