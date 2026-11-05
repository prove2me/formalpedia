-- Prove2me | solution 1 for Exits.stFoldUntilPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:00:16.249546+00:00
-- url     : https://prove2.me/submissions/30b5fd95-0a49-486b-9cbc-15cb823a14d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_Exits_Poly

set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
namespace Exits
theorem _root_.solution : StFoldUntilPoly := by
  intro α β γ τ _ _ _ _ _ _ _ _ start nxt M _ g stop c₀ hs hn hg hst hc
  exact ⟨IsPolyT.foldUntil hs hn hg hst hc⟩
end Exits
