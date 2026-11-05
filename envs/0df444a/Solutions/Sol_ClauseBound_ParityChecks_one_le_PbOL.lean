-- Prove2me | solution 1 for ClauseBound.ParityChecks.one_le_PbOL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:09.801018+00:00
-- url     : https://prove2.me/submissions/31e072a0-4e77-4786-9cd1-d718fe77ed39

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
theorem _root_.solution (hn : 1 ≤ n) {K : ℕ} (hK : 1 ≤ K) : 1 ≤ PbOL K n Δ := by
  unfold PbOL Pb
  have hg : 0 < 3 * K ^ 8 := by positivity
  have h1 : 1 ≤ qv (3 * K ^ 8) (7 * n) := by
    unfold qv
    exact (Nat.one_le_div_iff hg).2 (by omega)
  have h2 : 1 ≤ 2 * (2 + bitOL Δ) := by omega
  have h3 : 1 ≤ occOL n Δ + 4 := by omega
  exact Nat.mul_pos (Nat.mul_pos h2 h1) h3
end ClauseBound.ParityChecks
