-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sum_undRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:22.340543+00:00
-- url     : https://prove2.me/submissions/a5c28836-9af6-4d9c-bb26-9506af0809d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
import Theorems.Thm_ClauseBound_ParityChecks_Num_sum_split
import Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_early
import Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_mid
import Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_late

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (m e : ℕ) {j r : ℕ} (hj : j < r) : ∑ j' ∈ range r, undRow j (Dset m e) j' = (m - e) + (r - 1 - j) * m := by
  rw [sum_split _ hj, Finset.sum_eq_zero fun i hi => undRow_early (mem_range.1 hi), undRow_mid]
  simp [undRow_late]
end ClauseBound.ParityChecks.Num
