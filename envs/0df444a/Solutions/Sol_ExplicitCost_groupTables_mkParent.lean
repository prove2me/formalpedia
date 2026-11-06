-- Prove2me | solution 1 for ExplicitCost.groupTables_mkParent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:31:51.946585+00:00
-- url     : https://prove2.me/submissions/e8e0f2c2-e4ff-4b35-b05b-cc0b9c344eb8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_ExplicitCost_length_unary


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (D : PiecesCounted.Data) (c K g lam B : ℕ) (tr : Bool) (y x L : ℕ) (W : ℕ → List Bool → ℤ) :
    groupTables D c (mkParent D K g lam B tr y x) L W = fun γ Θ => if h : γ < K then
      (Value.groupClique asked.under (netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0 := by
  have key : ∀ K' g' lam' B' : ℕ, K' = K → g' = g → lam' = lam → B' = B →
      (fun (γ : ℕ) (Θ : List Bool) => if h : γ < K' then
        (Value.groupClique asked.under (netInput (patternNet D c g' tr lam' y W) (g' ^ 3 * lam') (bitsOne c g' lam' B')) (patternNet D c g' tr lam' y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0) =
      fun γ Θ => if h : γ < K then
        (Value.groupClique asked.under (netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0 := by
    rintro _ _ _ _ rfl rfl rfl rfl
    rfl
  exact key _ _ _ _ (length_unary K) (length_unary g) (length_unary lam) (length_unary B)
end ExplicitCost
