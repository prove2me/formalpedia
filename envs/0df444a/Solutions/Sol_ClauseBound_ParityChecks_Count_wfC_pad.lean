-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.wfC_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:09:19.856679+00:00
-- url     : https://prove2.me/submissions/a75aebca-17ea-4eb8-8b81-1c8c9ec324ae

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution {ψ : Fml} {r : ℕ} {Lam : List Chk} (hl : Lam.length ≤ r) (h : ∀ L ∈ Lam, ChkOK ψ.length L) :
    WfC ψ r (Lam ++ List.replicate (r - Lam.length) []) := by
  refine ⟨by rw [List.length_append, List.length_replicate]; omega, fun L hL => ?_⟩
  rcases List.mem_append.1 hL with h1 | h1
  · exact h L h1
  · rw [List.eq_of_mem_replicate h1]
    exact ⟨List.nodup_nil, fun e he => absurd he List.not_mem_nil⟩
end ClauseBound.ParityChecks.Count
