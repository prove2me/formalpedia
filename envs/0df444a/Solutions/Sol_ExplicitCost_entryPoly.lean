-- Prove2me | solution 1 for ExplicitCost.entryPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:10:15.9909+00:00
-- url     : https://prove2.me/submissions/b10c40ac-3c2a-40a5-a456-f1f21f81a15d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_PaddedDescent_F_CertNet
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Poly

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed PaddedDescent.F.CertNet
variable {α : Type} [Enc α]
namespace ExplicitCost
theorem _root_.solution : EntryPoly := ⟨entryDataCert⟩
end ExplicitCost
