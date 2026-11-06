-- Prove2me | solution 1 for ExplicitCost.total_direction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:09:29.149302+00:00
-- url     : https://prove2.me/submissions/a1cf76c7-6bb3-42fb-a6a0-2d778eb104cd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
import Theorems.Thm_ExplicitCost_rG_readyOf

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}
namespace ExplicitCost
theorem _root_.solution (hl : hLev h = l + 1) (y : ℕ) :
    totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ h, y)) 0 (hLam h) y =
      min (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y) (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y) := by
  have e : direction (readyOf D x₀ h, y) = decide (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y <
      totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y) := by
    unfold direction
    rw [rG_readyOf D x₀ h hl]
    rfl
  rw [e]
  by_cases hlt : totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y < totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y
  · rw [decide_eq_true hlt, min_eq_right hlt.le]
  · rw [decide_eq_false hlt, min_eq_left (not_lt.1 hlt)]
end ExplicitCost
