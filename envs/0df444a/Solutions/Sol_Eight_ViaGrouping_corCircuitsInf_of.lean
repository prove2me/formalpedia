-- Prove2me | solution 1 for Eight.ViaGrouping.corCircuitsInf_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:52:21.291984+00:00
-- url     : https://prove2.me/submissions/ed608761-6e83-418e-a1d7-863d59926a61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_ENP
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorENP
import Theorems.Thm_Eight_ViaGrouping_corCircuits_of
import Theorems.Thm_CircuitLowerBound_corCircuits_of
import Theorems.Thm_ENP_infinitely_often


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open ENP Groundwork Turing CircuitLowerBound
namespace Eight.ViaGrouping
theorem _root_.solution (hEng : StEngine) : ENP.CorCircuitsInf :=
  let ⟨L, h1, h2⟩ := corCircuits_of hEng
  ⟨L, h1, ENP.infinitely_often h2⟩
end Eight.ViaGrouping
