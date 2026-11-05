-- Prove2me | solution 1 for ClauseBound.Alg.NeedC.first_le_needG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:42:36.504742+00:00
-- url     : https://prove2.me/submissions/60fc758c-71a0-4cdf-bc16-e87ebf8772ca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F
namespace ClauseBound.Alg.NeedC
theorem _root_.solution (P : PiecesF) (Kup lam B cnt z : ℕ) (sched : List Step) :
    max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup))) ≤ needG P Kup lam B cnt z sched := by
  cases sched <;> exact le_max_left _ _
end ClauseBound.Alg.NeedC
