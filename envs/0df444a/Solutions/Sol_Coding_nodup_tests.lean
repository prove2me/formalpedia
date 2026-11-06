-- Prove2me | solution 1 for Coding.nodup_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:57.225199+00:00
-- url     : https://prove2.me/submissions/e11e6fa8-7cce-4e56-94df-93d14d77a0b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Coding_nodup_occIn
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_product
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.product



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}
namespace Coding
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (tests Φ).Nodup := ((nodup_occIn h3 0 Φ.length).product (nodup_occIn h3 0 Φ.length)).filter _
end Coding
