-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.getD_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:18:40.817412+00:00
-- url     : https://prove2.me/submissions/05dedc64-f1f8-46c2-a04f-b4fb34da79d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution {m : ℕ} {Lam : List Chk} (h : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < m) (j' : ℕ) :
    (Lam.getD j' []).Nodup ∧ ∀ x ∈ Lam.getD j' [], x < m := by
  rcases Nat.lt_or_ge j' Lam.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ hj]
    exact ⟨List.nodup_nil, fun x hx => absurd hx List.not_mem_nil⟩
end ClauseBound.ParityChecks.Shape
