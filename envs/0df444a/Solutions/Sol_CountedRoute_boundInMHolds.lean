-- Prove2me | solution 1 for CountedRoute.boundInMHolds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:01:02.211022+00:00
-- url     : https://prove2.me/submissions/936355ec-8d30-4945-b5ff-14209ac10715

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRoute_Defs
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_NamesInOrder_Main
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_CountedToPadded_Main
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedInstance_Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_CountedRoute_Main
import Theorems.Thm_CountedRoute_closedStatementsFrom
import Theorems.Thm_CountedRoute_onTheCountedRecursion

set_option autoImplicit false
section
section
open CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)
namespace CountedRoute
theorem _root_.solution : BoundInMHolds := (closedStatementsFrom onTheCountedRecursion).2.2.2
end CountedRoute
