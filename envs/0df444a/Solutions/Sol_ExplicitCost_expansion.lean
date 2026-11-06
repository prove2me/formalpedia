-- Prove2me | solution 1 for ExplicitCost.expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:59:23.780705+00:00
-- url     : https://prove2.me/submissions/e0c23974-36c3-4447-9164-7fb95d4ab913

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Expansion
import Theorems.Thm_ClauseBound_Alg_GridNet_ZW_mul_eq_sum
import Theorems.Thm_ClauseBound_Alg_GridNet_value_gridN
import Theorems.Thm_ExplicitCost_card_I_pos
import Theorems.Thm_ExplicitCost_cutsOK_piecesOf
import Theorems.Thm_ExplicitCost_sum_indexAt
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Printed_stCliqueValue
import Theorems.Thm_Value_stCliqueValue
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : Expansion := by
  intro ρ c x₀ D hS g lam W tr hg hlam
  have hC := cutsOK_piecesOf hS hlam [()]
  have hpos := card_I_pos hS.is hlam
  have hK : 2 ≤ g * g := by nlinarith
  have hA : ∀ x y u v, ∑ i ∈ range (#(D.fam lam).I - 1 + 1), (D.fam lam).A (indexAt D lam i) x y u v = (D.fam lam).d * Pieces.cross x y u v := by
    intro x y u v
    rw [Nat.sub_add_cancel hpos, sum_indexAt D lam fun i => (D.fam lam).A i x y u v, hS.is.sum lam hlam]
  have h := ZW_mul_eq_sum g g lam (listTables (g * g) W) (fun j => (D.fam lam).A (indexAt D lam j)) (#(D.fam lam).I - 1) (D.fam lam).d hA
  rw [Nat.sub_add_cancel hpos] at h
  rw [stCliqueValue (g * g) lam W hK hlam]
  refine h.trans (Finset.sum_congr rfl fun y _ => ?_)
  exact (value_gridN hC g g (tr y) y _).symm
end ExplicitCost
