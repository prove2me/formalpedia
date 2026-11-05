-- Prove2me | solution 1 for ClauseBound.TopN.stParN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:05.935146+00:00
-- url     : https://prove2.me/submissions/72aa1051-e985-4ec6-9f3e-a40b9e2c2aa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_TopN_Budget
import Theorems.Thm_ClauseBound_TopN_leafC_le
import Theorems.Thm_ClauseBound_TopN_last_le

set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN
open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)
namespace ClauseBound.TopN
theorem _root_.solution : StParN := fun k _ s => ⟨leafC_le k s, fun hn => last_le (betaN k s) hn⟩
end ClauseBound.TopN
