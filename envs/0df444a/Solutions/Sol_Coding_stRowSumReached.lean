-- Prove2me | solution 1 for Coding.stRowSumReached
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:03:04.031228+00:00
-- url     : https://prove2.me/submissions/cae8b311-2f4f-473b-9440-ed97956d2bf1

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
import Theorems.Thm_Coding_capF_eq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}
namespace Coding
theorem _root_.solution : StRowSumReached := by
  have hmu : mu 3 sixExample = 1 := by decide
  have h0 : (testsBetween 3 sixExample 1 0).length = 3 := by decide
  have h2 : (testsBetween 3 sixExample 1 2).length = 3 := by decide
  have hs : univ.erase (1 : Fin 3) = {0, 2} := by decide
  have h3 : ∀ C ∈ sixExample, C.length ≤ 3 := by decide
  refine ⟨hmu, ?_, ?_⟩
  · rw [hs, Finset.sum_pair (by decide), hmu]
    change (testsBetween 3 sixExample 1 0).length + (testsBetween 3 sixExample 1 2).length = 6 * 1
    rw [h0, h2]
  · rw [hs, Finset.sum_pair (by decide), hmu]
    change capF 3 3 sixExample 1 0 + capF 3 3 sixExample 1 2 = 6 * 1
    rw [capF_eq (by norm_num) h3, capF_eq (by norm_num) h3, h0, h2]
end Coding
