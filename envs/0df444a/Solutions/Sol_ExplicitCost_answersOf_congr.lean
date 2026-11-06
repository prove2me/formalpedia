-- Prove2me | solution 1 for ExplicitCost.answersOf_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:09:30.204714+00:00
-- url     : https://prove2.me/submissions/dc36f7d3-a424-4e24-8258-ad8f765a67c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {K lam : ℕ} {W W' : ℕ → List Bool → ℤ} (h : ∀ w < K, ∀ z ∈ words ((K - 1) * lam), W w z = W' w z) : answersOf K lam W = answersOf K lam W' := by
  funext q
  unfold answersOf tables
  by_cases hq : q.1 < K ∧ q.2.length = (K - 1) * lam
  · rw [if_pos hq, if_pos hq, h q.1 hq.1 q.2 (mem_words.2 hq.2)]
  · rw [if_neg hq, if_neg hq]
end ExplicitCost
