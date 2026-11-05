-- Prove2me | solution 1 for CountKSatRate.stRoundSEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:58:05.215496+00:00
-- url     : https://prove2.me/submissions/c263e430-1d60-4b3a-9e7d-e72edebd9502

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Walk
import Theorems.Thm_CountKSatRate_roundS_iterate_of_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSatRate
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)
namespace CountKSatRate
theorem _root_.solution : StRoundSEnd := fun _ step val d s hd R hR => roundS_iterate_of_le step val d s hd R hR
end CountKSatRate
