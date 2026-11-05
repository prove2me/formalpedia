-- Prove2me | solution 1 for ClauseBound.ParityChecks.BridgeInc.prod_J1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:14:04.828428+00:00
-- url     : https://prove2.me/submissions/79c715db-bb69-4629-947f-d736d4a4991e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc

set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.BridgeInc
theorem _root_.solution {r j : ℕ} (hj : j ≤ r) (g : ℕ → ℤ) : ∏ j' ∈ J1 r j, g j'.val = ∏ j' ∈ range j, g j' := by
  refine prod_bij (fun a _ => a.val) (fun a ha => mem_range.2 (mem_filter.1 ha).2) (fun a _ b _ hab => Fin.ext hab)
    (fun b hb => ⟨⟨b, (mem_range.1 hb).trans_le hj⟩, mem_filter.2 ⟨mem_univ _, mem_range.1 hb⟩, rfl⟩) fun _ _ => rfl
end ClauseBound.ParityChecks.BridgeInc
