-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.stBridgeF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:53:10.477706+00:00
-- url     : https://prove2.me/submissions/f9611091-c9b5-42fa-b924-177b0ca0ccb6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_choose
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_two_layers
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_Vof_eq_empty_iff
import Theorems.Thm_ClauseBound_ParityChecks_StepOne_product
import Theorems.Thm_Groundwork_PolyT_product
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.product



set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.Bridge
theorem _root_.solution : StBridgeF := by
  intro n r nb M ψ Lam hψ hW hG
  refine (two_layers hψ hW le_rfl M (-1) 0 nb (fun ξ => ∑ S ∈ (Vof ψ ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S)
    fun ξ => sum_Icc_choose _ _ _).trans ?_
  have e : ∑ ξ : Fin n → Bool, (∑ S ∈ (Vof ψ ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S) * ∏ j' ∈ range r, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) =
      (nSat n ψ : ℤ) := by
    rw [sum_congr rfl fun ξ _ => StepOne.product (Vof (n := n) ψ) nb r (Lof ψ Lam) hG ξ, sum_boole, nSat]
    exact congrArg (fun s : Finset (Fin n → Bool) => (#s : ℤ)) (filter_congr fun ξ _ => Vof_eq_empty_iff ψ ξ)
  rw [e]
end ClauseBound.ParityChecks.Bridge
