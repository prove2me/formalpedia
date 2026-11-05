-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.big_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:10:25.169974+00:00
-- url     : https://prove2.me/submissions/b8af0949-d22f-4320-a781-9b2dabee584f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution (n Δ : ℕ) : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) = 6 * n * (8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2))) + 8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2)) := by
  ring
end ClauseBound.ParityChecks.RunF
