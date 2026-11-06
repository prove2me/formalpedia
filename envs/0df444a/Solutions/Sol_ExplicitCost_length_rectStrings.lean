-- Prove2me | solution 1 for ExplicitCost.length_rectStrings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:56.388781+00:00
-- url     : https://prove2.me/submissions/d0e8c602-0692-43cc-8ed6-cd13d90d06f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {q : PsiQ} (ha : q.1.1 < nParts g g tr) (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hz' : q.2.2.length = nMemb g g tr * (g * g) * lam)
    {i i' : ℕ} (hi : i < nMemb g g tr) (hi' : i' < nMemb g g tr) :
    (rectStrings g tr lam q i i').1.length = lam ∧ (rectStrings g tr lam q i i').2.1.length = lam ∧ (rectStrings g tr lam q i i').2.2.1.length = lam ∧ (rectStrings g tr lam q i i').2.2.2.length = lam := by
  cases tr
  · exact ⟨length_heG hz hi (nodeG_lt false hb hi'), length_heG hz hi' (nodeG_lt false hb hi), length_heG hz' hi (nodeG_lt false ha hi'), length_heG hz' hi' (nodeG_lt false ha hi)⟩
  · exact ⟨length_heG hz hi (nodeG_lt true hb hi'), length_heG hz' hi (nodeG_lt true ha hi'), length_heG hz hi' (nodeG_lt true hb hi), length_heG hz' hi' (nodeG_lt true ha hi)⟩
end ExplicitCost
