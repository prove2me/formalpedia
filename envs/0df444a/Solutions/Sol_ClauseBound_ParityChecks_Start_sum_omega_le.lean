-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.sum_omega_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:40.19075+00:00
-- url     : https://prove2.me/submissions/eb31fa0a-a66c-4d8b-a56f-7fb44de7b368

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [DecidableEq E]
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution (V : X → Finset E) (nb : ℕ) :
    (∑ ξ, (omega V nb ξ : ℚ)) ≤ ((Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) : ℚ) := by
  have h : ∑ ξ, omega V nb ξ ≤ Fintype.card X * (Fintype.card E).choose (nb + 1) := by
    have := Finset.sum_le_card_nsmul (univ : Finset X) (omega V nb) ((Fintype.card E).choose (nb + 1))
      (fun ξ _ => Nat.choose_le_choose _ (Finset.card_le_univ _))
    simpa [Finset.card_univ] using this
  exact_mod_cast h
end ClauseBound.ParityChecks.Start
