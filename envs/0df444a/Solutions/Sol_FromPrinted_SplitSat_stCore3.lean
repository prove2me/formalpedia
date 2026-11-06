-- Prove2me | solution 1 for FromPrinted.SplitSat.stCore3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:55.393234+00:00
-- url     : https://prove2.me/submissions/8256a913-d43c-4856-95d9-17fbbe49c69e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_Printed_End
import Definitions.Def_Printed_Count
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_WidthK_Top_Poly
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Core
import Theorems.Thm_FromPrinted_SplitSat_core3_polyTimeSteps
import Theorems.Thm_FromPrinted_SplitSat_core3_decides
import Theorems.Thm_Exits_stDecides
import Theorems.Thm_Printed_stDecides


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping GraphProblems SplitSat
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution : StCore3 := fun _ hδ => by
  obtain ⟨ℓ, τ, -, h⟩ := Printed.stDecides _ hδ
  exact ⟨ℓ, τ, core3_polyTimeSteps ℓ τ, core3_decides h⟩
end FromPrinted.SplitSat
