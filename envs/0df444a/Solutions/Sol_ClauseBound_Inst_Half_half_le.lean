-- Prove2me | solution 1 for ClauseBound.Inst.Half.half_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:35:13.222534+00:00
-- url     : https://prove2.me/submissions/924b4b9a-3be6-43b4-b239-a23e20df037f

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
theorem _root_.solution : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 2 := by
  have h1 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by norm_num)) h1
end ClauseBound.Inst.Half
