-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:14:21.099949+00:00
-- url     : https://prove2.me/submissions/f6e84997-5a72-4f40-ae02-0cfc056a4920

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.Bridge
theorem _root_.solution {n r : ℕ} (F : (Fin n → Bool) → (Fin r → Bool) → ℤ) :
    ∑ σ : Fin (n + r) → Bool, F (xi σ) (yy σ) = ∑ ξ, ∑ y, F ξ y := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.appendEquiv n r).symm _ _ fun _ => rfl
end ClauseBound.ParityChecks.Bridge
