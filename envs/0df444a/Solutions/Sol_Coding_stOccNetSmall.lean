-- Prove2me | solution 1 for Coding.stOccNetSmall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:49:33.12119+00:00
-- url     : https://prove2.me/submissions/c83067c2-63f7-44d3-af4e-b4c1441c6865

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
import Theorems.Thm_Coding_length_occIn_le
import Theorems.Thm_Coding_boole_zero_or_one
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution : StOccNetSmall := by
  intro g Φ h3
  exact ⟨fun a => length_occIn_le h3 _ _, fun _ _ => boole_zero_or_one _, fun _ _ _ _ => boole_zero_or_one _, fun _ _ _ _ => boole_zero_or_one _⟩
end Coding
