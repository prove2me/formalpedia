-- Prove2me | solution 1 for ClauseBound.Alg.Grid.stGrid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:39.028365+00:00
-- url     : https://prove2.me/submissions/3aefd6a7-7db2-4747-941f-5730c916500a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_ClauseBound_Alg_Grid
import Theorems.Thm_ClauseBound_Alg_Grid_cutsOK_of_spec
import Theorems.Thm_ClauseBound_Alg_GridNet_U_gridN
import Theorems.Thm_ClauseBound_Alg_GridNet_ZW_mul_eq_sum
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c_le
import Theorems.Thm_ClauseBound_Alg_GridNet_gridN_sized
import Theorems.Thm_ClauseBound_Alg_GridNet_value_gridN
import Theorems.Thm_ClauseBound_Alg_GridPresents_presents
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_presents
import Theorems.Thm_PaddedDescent_F_RebalF_presents
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Grid
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
namespace ClauseBound.Alg.Grid
theorem _root_.solution (P : PiecesF) : StGrid P := by
  intro pad pu du hu ℓu T B _ hS hpad hB
  obtain ⟨A, hsum, hP⟩ := cutsOK_of_spec hS hpad
  have hc : P.cnt hu.length ℓu.length - 1 + 1 = P.cnt hu.length ℓu.length := Nat.sub_add_cancel hS.cnt_pos
  refine ⟨termZ pu.length du.length ℓu.length (instOf T) A (P.cnt hu.length ℓu.length - 1), ?_, fun y _ tr => ?_⟩
  · have h := ZW_mul_eq_sum pu.length du.length ℓu.length (instOf T) A (P.cnt hu.length ℓu.length - 1) (P.d hu.length ℓu.length)
      (by rw [hc]; exact hsum)
    rwa [hc] at h
  · exact ⟨gridN P pad pu.length du.length tr hu.length ℓu.length y (instOf T), GridPresents.presents P pad pu du hu ℓu tr y T,
      value_gridN hP _ _ tr y _, gridN_sized hP _ _ tr y hB, U_gridN P pad _ _ tr _ _ y _, fun a b _ => gridN_c_le hP _ _ tr y _ a b⟩
end ClauseBound.Alg.Grid
