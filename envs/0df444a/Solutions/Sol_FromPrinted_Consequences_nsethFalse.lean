-- Prove2me | solution 1 for FromPrinted.Consequences.nsethFalse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:30:52.077303+00:00
-- url     : https://prove2.me/submissions/0c192ae7-0de2-40ac-a7ea-7b5228cf93e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FromPrinted_SplitSat
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Definitions.Def_CountKSat_InOut
import Definitions.Def_WidthK_Decode
import Definitions.Def_FromPrinted_Verifier
import Theorems.Thm_FromPrinted_Consequences_stVerifier
import Theorems.Thm_FromPrinted_Consequences_stSmallWidths
import Theorems.Thm_FromPrinted_Consequences_nsethFrom

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Consequences
namespace FromPrinted.Consequences
theorem _root_.solution : NsethFalse := nsethFrom stVerifier stSmallWidths
end FromPrinted.Consequences
