-- Prove2me | solution 1 for CountKSatRate.Top.iterate_le_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:46:52.239331+00:00
-- url     : https://prove2.me/submissions/9df95a19-c25c-4009-b4c1-6fe0194a59dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Top
import Theorems.Thm_CountKSatRate_Top_le_roundS
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Top
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)
namespace CountKSatRate.Top
theorem _root_.solution {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) (i j : ℕ) :
    ((roundS step val)^[i] st).2 ≤ ((roundS step val)^[j + i] st).2 := by
  induction j with
  | zero => rw [Nat.zero_add]
  | succ j ih =>
    rw [Nat.succ_add, Function.iterate_succ_apply']
    exact ih.trans (le_roundS step val _)
end CountKSatRate.Top
