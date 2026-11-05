-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sub_undCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:42.499675+00:00
-- url     : https://prove2.me/submissions/5575968c-3761-400d-a063-3558765f7812

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {e j : ℕ} (hj : j < q.r) (x : Fin q.m) : q.r - undCol q.r j (Dset q.m e) x = j + if x.val < e then 1 else 0 := by
  unfold undCol Dset
  simp only [mem_filter, mem_univ, true_and]
  by_cases h : e ≤ x.val
  · rw [if_pos h, if_neg (by omega)]; omega
  · rw [if_neg h, if_pos (by omega)]; omega
end ClauseBound.ParityChecks.Num
