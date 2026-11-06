-- Prove2me | solution 1 for ExplicitCost.child_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:36:10.761632+00:00
-- url     : https://prove2.me/submissions/7a9dc999-79b4-48fa-963b-cae0369baa7c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
import Theorems.Thm_ExplicitCost_length_unary
import Theorems.Thm_ExplicitCost_groupTables_value

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) (a' : Ctx) (f : TableQuery → Option Ans) {K g lam B L y x : ℕ} {tr : Bool} (hK : Levels.Gen.K x₀ (cLev a') = K)
    (hp : parentOf a' = mkParent D K g lam B tr y x) (hL : cLam a' = L) (hK0 : 0 < K) :
    (spec D c x₀ Bound).val a' ((spec D c x₀ Bound).tab a' f) =
      .inl (Value.groupClique asked.under (netInput (patternNet D c g tr lam y (readTables f)) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y (readTables f)) hK0 x L).value := by
  have h := groupTables_value D c (mkParent D K g lam B tr y x) L (readTables f)
  unfold netP netB at h
  rw [show pK (mkParent D K g lam B tr y x) = K from length_unary K, show pG (mkParent D K g lam B tr y x) = g from length_unary g, show pLam (mkParent D K g lam B tr y x) = lam from length_unary lam,
    show pB (mkParent D K g lam B tr y x) = B from length_unary B, show pTr (mkParent D K g lam B tr y x) = tr from rfl, show pY (mkParent D K g lam B tr y x) = y from rfl,
    show pX (mkParent D K g lam B tr y x) = x from rfl] at h
  rw [← h hK0]
  show Sum.inl (clique (Levels.Gen.K x₀ (cLev a')) (cLam a') fun w => readTables (answersOf (pK (parentOf a')) (cLam a') (groupTables D c (parentOf a') (cLam a') (readTables f))) w.val).value = _
  rw [hp, hL, hK, show pK (mkParent D K g lam B tr y x) = K from length_unary K]
end ExplicitCost
