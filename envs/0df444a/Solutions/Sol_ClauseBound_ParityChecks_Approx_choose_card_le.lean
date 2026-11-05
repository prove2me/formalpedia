-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.choose_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:03.162023+00:00
-- url     : https://prove2.me/submissions/8d39803a-2c43-4d9a-8e46-0b0e34b04d8b

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
omit [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (s : Finset E) (i : ℕ) : (#s).choose i ≤ (Fintype.card E).choose i :=
  Nat.choose_le_choose _ (Finset.card_le_univ _)
end ClauseBound.ParityChecks.Approx
