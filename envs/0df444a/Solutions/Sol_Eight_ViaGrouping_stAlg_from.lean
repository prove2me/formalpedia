-- Prove2me | solution 1 for Eight.ViaGrouping.stAlg_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:20.541753+00:00
-- url     : https://prove2.me/submissions/b25af71b-d6dd-49f1-ba37-ae71020b0f27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_ENP
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorENP
import Theorems.Thm_CircuitLowerBound_stCertSched
import Theorems.Thm_CircuitLowerBound_stFlip
import Theorems.Thm_CircuitLowerBound_stForm
import Theorems.Thm_CircuitLowerBound_stNorm
import Theorems.Thm_Eight_stAlg_of


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open ENP Groundwork Turing CircuitLowerBound
namespace Eight.ViaGrouping
theorem _root_.solution (hEng : StEngine) : StAlg := Eight.stAlg_of hEng stForm stNorm stCertSched stFlip
end Eight.ViaGrouping
