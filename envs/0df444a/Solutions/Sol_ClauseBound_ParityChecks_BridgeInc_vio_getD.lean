-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.vio_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:44.176194+00:00
-- url     : https://prove2.me/submissions/ccbbd385-a145-4370-9448-9bab91b3e4ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_vio_ext
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {n r : ℕ} (σ : Fin (n + r) → Bool) {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (e : ℕ) :
    vio (ext σ) (ψ.getD e []) = vio (ext (xi σ)) (ψ.getD e []) := by
  refine vio_ext σ fun l hl => ?_
  by_cases he : e < ψ.length
  · rw [List.getD_eq_getElem _ _ he] at hl
    exact h _ (List.getElem_mem he) l hl
  · rw [List.getD_eq_default _ _ (by omega)] at hl
    exact absurd hl (List.not_mem_nil)
end ClauseBound.ParityChecks.BridgeInc
