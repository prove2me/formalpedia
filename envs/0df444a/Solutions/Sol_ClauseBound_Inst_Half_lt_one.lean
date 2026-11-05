-- Prove2me | solution 1 for ClauseBound.Inst.Half.lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:35:25.257945+00:00
-- url     : https://prove2.me/submissions/8ec3248c-43a6-4ee3-8617-ea5c0bc204c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Inst_HalfEnd

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
namespace ClauseBound.Inst.Half
theorem _root_.solution : 1 / Real.sqrt 2 < 1 := by
  have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  rw [div_lt_one (by linarith)]
  exact h1
end ClauseBound.Inst.Half
