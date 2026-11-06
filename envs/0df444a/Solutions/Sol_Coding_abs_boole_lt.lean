-- Prove2me | solution 1 for Coding.abs_boole_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:39.037392+00:00
-- url     : https://prove2.me/submissions/68f50a43-9bb3-4b95-a350-f0acebe7ad83

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| < 2 ^ 1 := by split_ifs <;> norm_num
end Coding
