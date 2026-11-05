-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.abs_prod_ev_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:48.391227+00:00
-- url     : https://prove2.me/submissions/38a2a8f9-0d0e-4888-9d81-1af2b24ce2ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Theorems.Thm_ClauseBound_ParityChecks_Approx_ev_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Approx_ev_le_one

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (s : Finset ℕ) (q : ℕ → ℕ) : |∏ i ∈ s, ev (q i)| ≤ 1 := by
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => ev_nonneg _)]
  exact Finset.prod_le_one (fun i _ => ev_nonneg _) fun i _ => ev_le_one _
end ClauseBound.ParityChecks.Approx
