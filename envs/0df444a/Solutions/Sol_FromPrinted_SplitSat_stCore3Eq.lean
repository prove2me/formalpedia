-- Prove2me | solution 1 for FromPrinted.SplitSat.stCore3Eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:35:04.080396+00:00
-- url     : https://prove2.me/submissions/11bc7463-12ad-4700-adaf-771b92ec65a0

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

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping GraphProblems SplitSat
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution : StCore3Eq := fun _ _ => rfl
end FromPrinted.SplitSat
