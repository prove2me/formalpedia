-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.Upar_fresh_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:19:04.847204+00:00
-- url     : https://prove2.me/submissions/855161c0-09a4-418a-8a69-bdf02a7b6e7d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_ev_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Start_term_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (hnb : 2 ≤ nb) (hΛ : Λ j = ∅) :
    Upar V nb r j Λ univ ≤
      (5 / 8) ^ (r - 1 - j) * (5 / 8 * ∑ ξ, (omega V nb ξ : ℚ) * ∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) := by
  unfold Upar
  rw [Finset.mul_sum (a := (5 / 8 : ℚ))]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ξ _ => ?_) (by positivity)
  rw [hΛ]
  simp only [empty_inter, card_empty, pow_zero, one_mul, univ_inter]
  have := term_le nb #(V ξ) hnb (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) (Finset.prod_nonneg fun _ _ => ev_nonneg _)
  unfold omega
  linarith
end ClauseBound.ParityChecks.Start
