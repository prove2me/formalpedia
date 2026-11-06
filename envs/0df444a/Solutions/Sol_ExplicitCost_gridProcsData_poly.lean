-- Prove2me | solution 1 for ExplicitCost.gridProcsData_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:57.126585+00:00
-- url     : https://prove2.me/submissions/1e154ba0-89fb-45c7-9803-6e651523559b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyQueries
import Definitions.Def_CountedRecursion_PolyRules
import Definitions.Def_ExplicitCost_Poly
import Definitions.Def_Printed_HandOver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyProcedure
import Theorems.Thm_ExplicitCost_rowWeight_poly
import Theorems.Thm_ExplicitCost_rowPair_poly
import Theorems.Thm_ExplicitCost_rowFactor_poly
import Theorems.Thm_ExplicitCost_rowMem_poly
import Theorems.Thm_Printed_answer_poly


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (c : ℕ) : (gridProcsData c).answer.PolyTimeSteps :=
  answer_poly (gridProcsData c) (rowMem_poly c) rowWeight_poly rowPair_poly rowFactor_poly
end ExplicitCost
