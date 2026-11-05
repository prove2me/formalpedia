-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.getD_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:13:02.786117+00:00
-- url     : https://prove2.me/submissions/11e0fb37-e40f-4f94-b557-01264d1e7cce

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
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (hψ : WfL k n [ψ]) (x : ℕ) : ∀ l ∈ ψ.getD x [], l.1 < n := by
  rcases Nat.lt_or_ge x ψ.length with hx | hx
  · rw [List.getD_eq_getElem _ _ hx]
    exact (hψ ψ List.mem_cons_self _ (List.getElem_mem hx)).2.2
  · rw [List.getD_eq_default _ _ hx]
    exact fun l hl => absurd hl List.not_mem_nil
end ClauseBound.ParityChecks.Shape
