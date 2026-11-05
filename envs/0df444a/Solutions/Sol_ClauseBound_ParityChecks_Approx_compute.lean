-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.compute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:42.146549+00:00
-- url     : https://prove2.me/submissions/c61f270d-0246-45a6-809e-d3960bec98e2

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
omit [Fintype E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) :
    tUpar V nb r i₀ j Λ D =
      (5 / 8) ^ (r - 1 - j) * (1 / 2) * ((Aint V nb j Λ : ℚ) + ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (Bint V nb i j Λ D : ℚ)) := by
  unfold tUpar Aint Bint
  push_cast
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring
end ClauseBound.ParityChecks.Approx
