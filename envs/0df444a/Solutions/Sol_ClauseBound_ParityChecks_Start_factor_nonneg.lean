-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.factor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:10:37.308959+00:00
-- url     : https://prove2.me/submissions/445408a3-6900-447a-a9da-c8e57819974a

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
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (a u : ℕ) : 0 ≤ 1 / 2 * (1 + (-1) ^ a * t ^ u) := by
  have h2 : t ^ u ≤ 1 := pow_le_one₀ h0 h1
  have h3 : 0 ≤ t ^ u := pow_nonneg h0 u
  rcases neg_one_pow_eq_or ℚ a with h | h <;> rw [h] <;> linarith
end ClauseBound.ParityChecks.Start
