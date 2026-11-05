-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.runF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:41:09.486793+00:00
-- url     : https://prove2.me/submissions/f216ad31-45f0-4a58-8254-b159c43bd4c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_runC_eq
import Theorems.Thm_ClauseBound_ParityChecks_RunF_lenChk_le_big
import Theorems.Thm_ClauseBound_ParityChecks_RunF_all_le_big
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par) (ψ : Fml)
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution (hF : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ pad.length) (hr : q.r ≤ 6 * n) (hm : q.m ≤ Δ * n) :
    runF S k pad i n Δ q ψ = q.run (orcA S k pad i n Δ q ψ) (orcB S k pad i n Δ q ψ) :=
  runC_eq ((all_le_big hr hm).trans hF) ((lenChk_le_big hm).trans hF)
end ClauseBound.ParityChecks.RunF
