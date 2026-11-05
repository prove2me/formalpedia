-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.five_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:13:19.512044+00:00
-- url     : https://prove2.me/submissions/baaf767f-0afb-4f9a-8a00-698894a83257

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_pow_lt_quarter

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution : ∀ nb v : ℕ, 2 ≤ nb → nb < v → 1 / 2 * (1 + (1 - 2 * pr nb) ^ v) < 5 / 8 := by
  intro nb v hnb hv
  have key : ((1 : ℚ) - 2 * pr nb) ^ v < 1 / 4 := by
    have h : ((((1 : ℚ) - 2 * (1 / nb)) ^ v : ℚ) : ℝ) < ((1 / 4 : ℚ) : ℝ) := by
      have := pow_lt_quarter nb v hnb hv
      push_cast
      have e : (1 : ℝ) - 2 * (1 / nb) = 1 - 2 / nb := by ring
      rw [e]; exact this
    unfold pr
    exact_mod_cast h
  linarith
end ClauseBound.ParityChecks.Start
