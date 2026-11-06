-- Prove2me | solution 1 for FromPrinted.SplitCount.COUNT_polyTimeSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:47:46.818909+00:00
-- url     : https://prove2.me/submissions/52f9fa2e-7c2d-4ac0-90e7-4af4470cfd8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Printed_End
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Count
import Theorems.Thm_Exits_stClique
import Theorems.Thm_Printed_firstLine_poly
import Theorems.Thm_Printed_onFormula_poly
import Theorems.Thm_Printed_stClique
import Theorems.Thm_Printed_stGroupingPoly


set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace FromPrinted.SplitCount
theorem _root_.solution (ℓ : ℕ) : PolyTimeSteps (Printed.COUNT ℓ) :=
  Printed.firstLine_poly (Printed.onFormula_poly _ 3 _ (Printed.stGroupingPoly _ _ _ (Printed.stClique ℓ).1))
end FromPrinted.SplitCount
