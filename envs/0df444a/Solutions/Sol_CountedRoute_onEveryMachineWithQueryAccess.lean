-- Prove2me | solution 1 for CountedRoute.onEveryMachineWithQueryAccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:19:19.618563+00:00
-- url     : https://prove2.me/submissions/bd4f10b8-1f06-43f3-a321-430aab174754

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
import Theorems.Thm_CountedRoute_onEveryMachineWithQueryAccessFrom
import Theorems.Thm_MainRoute_bothBoundsOnEverySolver
import Theorems.Thm_NamesInOrder_onEverySolver
import Theorems.Thm_QueryMachines_Bridge_cutNumberFacts
import Theorems.Thm_QueryMachines_Bridge_solverOfMachineLevels


set_option autoImplicit false
section
section
open CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)
namespace CountedRoute
theorem _root_.solution : OnEveryMachineWithQueryAccess := onEveryMachineWithQueryAccessFrom solverOfMachineLevels cutNumberFacts bothBoundsOnEverySolver onEverySolver
end CountedRoute
