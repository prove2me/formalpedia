-- Prove2me | solution 1 for Coding.occOfSlot_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:41:06.866201+00:00
-- url     : https://prove2.me/submissions/8c345b9c-552d-41a9-b7ef-c409b27eafa7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Coding_place_occOfSlot
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_SatNet_idx_injective
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}
namespace Coding
theorem _root_.solution {m : ℕ} : Function.Injective (occOfSlot (m := m)) := fun p q h =>
  idx_injective (by rw [← place_occOfSlot, ← place_occOfSlot, h])
end Coding
