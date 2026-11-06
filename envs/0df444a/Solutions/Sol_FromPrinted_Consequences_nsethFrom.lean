-- Prove2me | solution 1 for FromPrinted.Consequences.nsethFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:34.356951+00:00
-- url     : https://prove2.me/submissions/6dc2b7dc-5be2-4119-96d2-33e27fc04c7c

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
import Theorems.Thm_Eight_ViaGrouping_not_NSETH_TM_of


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Consequences
namespace FromPrinted.Consequences
theorem _root_.solution (hV : StVerifier) (hS : StSmallWidths) : NsethFalse := by
  refine not_NSETH_TM_of fun k hk δ hδ => ?_
  by_cases h3 : k ≤ 3
  · obtain ⟨ℓ, τ, c, hp, hc⟩ := hS k hk h3 δ hδ
    exact ⟨_, hp, c, hc⟩
  · obtain ⟨τ, ℓ₃, τ₃, c, hp, hc, -, -⟩ := hV k (by omega) δ hδ
    exact ⟨_, hp, c, hc⟩
end FromPrinted.Consequences
