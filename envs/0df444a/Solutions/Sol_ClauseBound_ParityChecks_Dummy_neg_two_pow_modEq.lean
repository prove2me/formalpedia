-- Prove2me | solution 1 for ClauseBound.ParityChecks.Dummy.neg_two_pow_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:04.893195+00:00
-- url     : https://prove2.me/submissions/91de9b73-6aae-49a6-bc6b-fee2e6579997

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Dummy
theorem _root_.solution {M k : ℕ} : (-2 : ℤ) ^ k ≡ (if k ≤ M then (-2 : ℤ) ^ k else 0) [ZMOD 2 ^ (M + 1)] := by
  split_ifs with hk
  · exact Int.ModEq.refl _
  · refine Int.modEq_zero_iff_dvd.2 ?_
    exact (pow_dvd_pow_of_dvd (by norm_num : (2 : ℤ) ∣ -2) (M + 1)).trans (pow_dvd_pow _ (by omega))
end ClauseBound.ParityChecks.Dummy
