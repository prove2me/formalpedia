-- Prove2me | solution 1 for ClauseBound.ParityChecks.two_le_LD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:46:07.343197+00:00
-- url     : https://prove2.me/submissions/60f7547c-2ae1-42cf-b650-716a5d388ce7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}
namespace ClauseBound.ParityChecks
theorem _root_.solution (hΔ : 2 ≤ Δ) : 2 ≤ LD Δ := by
  have h : Nat.clog 2 (2 ^ 2) ≤ Nat.clog 2 (2 * Δ) := Nat.clog_mono_right 2 (by omega)
  rwa [Nat.clog_pow 2 2 (by norm_num)] at h
end ClauseBound.ParityChecks
