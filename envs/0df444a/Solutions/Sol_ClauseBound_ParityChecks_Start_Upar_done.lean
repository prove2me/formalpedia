-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.Upar_done
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:45.334626+00:00
-- url     : https://prove2.me/submissions/1738481c-1502-44b1-a088-9e64810e6df7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_half_ev

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) :
    Upar V nb r j Λ ∅ = (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * ∏ j' ∈ range (j + 1), (ev #(Λ j' ∩ V ξ) : ℚ) := by
  unfold Upar
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.prod_range_succ, ← half_ev #(Λ j ∩ V ξ)]
  simp only [empty_inter, card_empty, pow_zero, mul_one]
  ring
end ClauseBound.ParityChecks.Start
