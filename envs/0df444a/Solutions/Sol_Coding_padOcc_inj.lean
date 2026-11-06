-- Prove2me | solution 1 for Coding.padOcc_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:39:56.089684+00:00
-- url     : https://prove2.me/submissions/d3b9fb0b-6aae-4794-a4e9-49f5005db8b1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Coding_getD_padOcc_occ
import Theorems.Thm_Coding_ext_getD
import Theorems.Thm_Coding_nodup_occIn
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) {z z' : List Bool} (hz : z.length = (occOf g Φ a.val).length) (hz' : z'.length = (occOf g Φ a.val).length)
    (h : padOcc g Φ a z = padOcc g Φ a z') : z = z' := by
  refine ext_getD (hz.trans hz'.symm) fun t ht => ?_
  rw [hz] at ht
  have ho := List.getElem_mem ht
  have h1 := getD_padOcc_occ h3 a z ho
  rw [h, getD_padOcc_occ h3 a z' ho] at h1
  unfold bitAt at h1
  have hnd : (occOf g Φ a.val).Nodup := nodup_occIn h3 _ _
  rw [hnd.idxOf_getElem t ht] at h1
  exact h1.symm
end Coding
