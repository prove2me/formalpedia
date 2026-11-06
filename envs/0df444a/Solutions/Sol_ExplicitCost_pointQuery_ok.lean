-- Prove2me | solution 1 for ExplicitCost.pointQuery_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:25:51.279697+00:00
-- url     : https://prove2.me/submissions/fcf75225-b774-4ae6-a74e-b3619a1c8bec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
import Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_map_range_eq_ofFn
import Theorems.Thm_Printed_length_flatten_ofFn
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) {i : ℕ} (hi : i < nMemb g g tr) :
    (toTable (pointQuery g tr lam (a.val, z) i)).1 < g * g ∧ (toTable (pointQuery g tr lam (a.val, z) i)).2.length = (g * g - 1) * lam := by
  have hn : nodeG g tr a i < g * g := nodeG_lt tr a.2 hi
  refine ⟨hn, ?_⟩
  change ((List.range (g * g)).map fun u => if u = nodeG g tr a i then [] else heG g g lam z i u).flatten.length = _
  rw [map_range_eq_ofFn]
  refine length_flatten_ofFn ⟨nodeG g tr a i, hn⟩ _ (fun u hu => ?_) (if_pos rfl)
  rw [if_neg fun e => hu (Fin.ext e)]
  exact length_heG hz hi u.2
end ExplicitCost
