-- Prove2me | solution 1 for CountKSatRate.stRoundS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:55:31.446393+00:00
-- url     : https://prove2.me/submissions/92f87930-83e2-4da0-a5ea-132ca2eb0bb0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Walk
import Theorems.Thm_CountKSatRate_roundS_iterate
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSatRate
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)
namespace CountKSatRate
theorem _root_.solution : StRoundS := fun _ step val i st out => roundS_iterate step val i st out
end CountKSatRate
