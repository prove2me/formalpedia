-- Prove2me | solution 1 for Coding.stOccNetCountsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:25:24.506894+00:00
-- url     : https://prove2.me/submissions/4453ef89-33cd-46be-94e2-8ffa39562a91

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
import Theorems.Thm_Eight_ViaGrouping_satNet_isNetworkP
import Theorems.Thm_Eight_network_value_eq
import Theorems.Thm_Eight_numSat_pos_iff
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution : StOccNetCountsOf := by
  intro HO HP g Φ hg h3
  have hv : (occNet g Φ).value = (Eight.numSat Φ : ℤ) := by
    rw [← (HP g _ _ _ (HO g Φ hg h3)).1, (satNet_isNetworkP hg 3 Φ).2.1]
    exact Eight.network_value_eq hg Φ h3
  refine ⟨hv, ?_⟩
  rw [hv, Nat.cast_pos]
  exact Eight.numSat_pos_iff Φ
end Coding
