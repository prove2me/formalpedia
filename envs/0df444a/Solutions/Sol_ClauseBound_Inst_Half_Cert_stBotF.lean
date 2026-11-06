-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.stBotF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:00.88361+00:00
-- url     : https://prove2.me/submissions/e15bf30b-de4a-4a1f-bd2c-b8feac1e413a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_botF_polyT


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution : StBotF := fun _ _ _ _ _ _ _ _ _ _ hp hW hf hh hμ hr hπ hσ => botF_polyT hp hW hf hh hμ hr hπ hσ
end ClauseBound.Inst.Half.Cert
