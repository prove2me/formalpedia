-- Prove2me | solution 1 for ClauseBound.Inst.Half.stVal_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:45.923203+00:00
-- url     : https://prove2.me/submissions/3949220a-3843-42d3-bfd3-0808c65c1a25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfSpec
import Definitions.Def_ClauseBound_Inst_HalfFact
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfPad
import Definitions.Def_ClauseBound_Inst_HalfPar
import Definitions.Def_ClauseBound_Inst_HalfAll
import Theorems.Thm_ClauseBound_Inst_Half_stBotF
import Theorems.Thm_ClauseBound_Inst_Half_stEnc
import Theorems.Thm_ClauseBound_Inst_Half_stTopF
import Theorems.Thm_ClauseBound_Inst_Half_stVal


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
namespace ClauseBound.Inst.Half
theorem _root_.solution : StVal := stVal stTopF stBotF stEnc
end ClauseBound.Inst.Half
