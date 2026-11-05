-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.omega_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:40.967313+00:00
-- url     : https://prove2.me/submissions/29b12fd4-9c29-4d46-8910-31873754b15a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X] [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (V : X → Finset E) (nb : ℕ) (ξ : X) : omega V nb ξ ≤ (Fintype.card E).choose (nb + 1) :=
  Nat.choose_le_choose _ (Finset.card_le_univ _)
end ClauseBound.ParityChecks.Approx
