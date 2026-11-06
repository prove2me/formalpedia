-- Prove2me | solution 1 for ExplicitCost.sumAndDivide_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:45:37.724378+00:00
-- url     : https://prove2.me/submissions/531cfa44-6d6f-419a-82bb-be84bb56769b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolySolverData
import Definitions.Def_CountedRecursion_PolyRules
import Definitions.Def_CountedRecursion_Numbers
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolySolver
import Theorems.Thm_ExplicitCost_patternValue_poly
import Theorems.Thm_ExplicitCost_bind_poly
import Theorems.Thm_ExplicitCost_divide_polyT
import Theorems.Thm_ExplicitCost_nPatterns_polyT
import Theorems.Thm_ExplicitCost_ofFun_poly
import Theorems.Thm_ExplicitCost_sumRange_poly


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hG : groupingCall.PolyTimeSteps) (c : ℕ) : (sumAndDivide c).PolyTimeSteps :=
  bind_poly (sumRange_poly nPatterns_polyT (patternValue_poly hG c)) (ofFun_poly divide_polyT)
end ExplicitCost
