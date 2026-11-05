-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.vio_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:11.097208+00:00
-- url     : https://prove2.me/submissions/efd6e44a-1015-4d5a-b0a6-98954e69d45e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_ext_lt

set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {n r : ℕ} (σ : Fin (n + r) → Bool) {C : Cl} (h : ∀ l ∈ C, l.1 < n) : vio (ext σ) C = vio (ext (xi σ)) C := by
  unfold vio
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun l hl => by rw [ext_lt σ (h l hl)]
end ClauseBound.ParityChecks.BridgeInc
