-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.partH_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:58.632085+00:00
-- url     : https://prove2.me/submissions/ec6e4acb-c46f-4543-8c78-5efee06c6bb2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_partH_polyT_of
import Theorems.Thm_ClauseBound_Inst_Half_Cert_stTopF
import Theorems.Thm_ClauseBound_Inst_Half_Cert_stBotF

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution (c₀ : ℕ) (top : Bool) : PolyT (partH c₀ top) := partH_polyT_of stTopF stBotF c₀ top
end ClauseBound.Inst.Half.Cert
