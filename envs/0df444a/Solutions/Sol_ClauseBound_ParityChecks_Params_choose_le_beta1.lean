-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.choose_le_beta1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:36:21.402058+00:00
-- url     : https://prove2.me/submissions/609c6528-bfd7-4e18-b1b1-ab7bad390087

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution (m i₀ i : ℕ) (hi : i ≤ i₀) : m.choose i ≤ 2 ^ beta1 m i₀ := by
  refine le_trans (Nat.le_pow_clog (by norm_num) _) (Nat.pow_le_pow_right (by norm_num) ?_)
  exact Finset.le_sup (f := fun i => Nat.clog 2 (m.choose i)) (mem_range.2 (by omega))
end ClauseBound.ParityChecks.Params
