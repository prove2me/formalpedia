-- Prove2me | solution 1 for Coding.stOccNetCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:32:22.479197+00:00
-- url     : https://prove2.me/submissions/a5ba5496-f558-43e0-85cd-0840d7976bbe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Occ
import Definitions.Def_Coding_Padding
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccMore
import Theorems.Thm_Coding_stOccNetCountsOf
import Theorems.Thm_Coding_stOccNet
import Theorems.Thm_Coding_stPaddingValue
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution : StOccNetCounts := stOccNetCountsOf stOccNet stPaddingValue
end Coding
