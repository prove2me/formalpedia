-- Prove2me | solution 1 for CountKSatRate.Top.iterate_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:48:26.58049+00:00
-- url     : https://prove2.me/submissions/77fc0237-0f15-43dc-b2bb-3bb673adf23d

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
import Theorems.Thm_CountKSatRate_Top_iterate_le_iterate
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Top
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)
namespace CountKSatRate.Top
theorem _root_.solution (hE : StRoundSEnd) {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) : ((roundS step val)^[i] ([s], 0)).2 ≤ ((leaves step d s).map val).sum := by
  have h := iterate_le_iterate step val ([s], 0) i (2 * (leaves step d s).length - 1)
  rwa [hE σ step val d s hd _ (Nat.le_add_right _ _)] at h
end CountKSatRate.Top
