-- Prove2me | solution 1 for FromPrinted.SplitSat.eth_and_seth_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:17.595823+00:00
-- url     : https://prove2.me/submissions/ec16a67e-aa19-45e4-ab5c-6123eafa44b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_Printed_End
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_FromPrinted_SplitSat
import Theorems.Thm_FromPrinted_SplitSat_stTiedTM
import Theorems.Thm_FromPrinted_SplitSat_stTiedThreeTM
import Theorems.Thm_FromPrinted_SplitSat_endFrom
import Theorems.Thm_SplitSat_endFrom
import Theorems.Thm_SplitSat_stTiedTM
import Theorems.Thm_SplitSat_stTiedThreeTM


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution : ThreeSatStatement := endFrom stTiedTM stTiedThreeTM
end FromPrinted.SplitSat
