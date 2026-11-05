-- Prove2me | solution 1 for CountKSatRate.stWalkS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:03.65657+00:00
-- url     : https://prove2.me/submissions/105cb5c9-a689-43a6-8795-b72f9b7fd731

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Walk
import Theorems.Thm_CountKSatRate_roundS_iterate_of_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Top_foldl_capped_eq_iterate
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open CountKSatRate
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)
namespace CountKSatRate
theorem _root_.solution : StWalkS := by
  intro k pad τ val r d hd hlen hst
  unfold walkS
  rw [Top.foldl_capped_eq_iterate (cap pad ([], 0)) (roundS (stepC (theta τ) k) val) (fun x => len x ≤ pad.length)
    (fun x hx => cap_eq hx) pad ([r], 0) (fun i _ => hst i),
    roundS_iterate_of_le (stepC (theta τ) k) val d r hd pad.length (by omega)]
end CountKSatRate
