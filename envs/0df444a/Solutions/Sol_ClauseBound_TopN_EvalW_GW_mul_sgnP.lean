-- Prove2me | solution 1 for ClauseBound.TopN.EvalW.GW_mul_sgnP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:13:19.828199+00:00
-- url     : https://prove2.me/submissions/008eeb7c-0b31-41aa-9b68-991d13122051

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Pi_layer_lt
import Theorems.Thm_PaddedDescent_F_Mark_Pi_prod_sign
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
namespace ClauseBound.TopN.EvalW
theorem _root_.solution (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) :
    GW Ls.length ws lo hi (fun i => (layP Ls P i).card) * sgnP Ls P =
      ∏ i ∈ range Ls.length, if lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0 then ws.getD i 0 ^ (layP Ls P i).card else 0 := by
  have h1 := Pi.prod_sign (fun e => (clAt Ls e).1) Ls.length P fun e he => Pi.layer_lt Ls (mem_range.1 (hP he))
  unfold GW sgnP
  rw [← h1, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  change (if lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0 then (ws.getD i 0 * (if i = 0 then 1 else -1)) ^ (layP Ls P i).card else 0) *
    (if i = 0 then (1 : ℤ) else -1) ^ (layP Ls P i).card = _
  by_cases hc : lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0
  · rw [if_pos hc, if_pos hc, ← mul_pow, mul_assoc]
    have h2 : (if i = 0 then (1 : ℤ) else -1) * (if i = 0 then (1 : ℤ) else -1) = 1 := by split_ifs <;> norm_num
    rw [h2, mul_one]
  · rw [if_neg hc, if_neg hc, zero_mul]
end ClauseBound.TopN.EvalW
