-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.getD_append_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:19.637574+00:00
-- url     : https://prove2.me/submissions/14ff431a-3b8a-4fb9-a622-b17898083d10

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (Ls : List Chk) (c : Chk) {j : ℕ} (hj : j ≠ Ls.length) : (Ls ++ [c]).getD j [] = Ls.getD j [] := by
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
end ClauseBound.ParityChecks.Run
