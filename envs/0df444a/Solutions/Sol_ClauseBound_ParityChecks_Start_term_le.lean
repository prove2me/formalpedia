-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:12.000204+00:00
-- url     : https://prove2.me/submissions/a7a46270-d87b-443e-9fa6-825286de908a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_five_eighths

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution (nb v : ℕ) (hnb : 2 ≤ nb) (c : ℚ) (hc : 0 ≤ c) :
    ((v.choose (nb + 1) : ℕ) : ℚ) * c * (1 / 2 * (1 + (1 - 2 * pr nb) ^ v)) ≤ ((v.choose (nb + 1) : ℕ) : ℚ) * c * (5 / 8) := by
  rcases Nat.lt_or_ge nb v with h | h
  · have := (five_eighths nb v hnb h).le
    gcongr
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
end ClauseBound.ParityChecks.Start
