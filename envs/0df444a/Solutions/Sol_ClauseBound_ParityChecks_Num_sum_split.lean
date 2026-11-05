-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:42:34.072728+00:00
-- url     : https://prove2.me/submissions/c9e6f036-0894-408e-b410-d7385b975aab

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
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution {M : Type} [AddCommMonoid M] (f : ℕ → M) {j r : ℕ} (hj : j < r) :
    ∑ i ∈ range r, f i = ∑ i ∈ range j, f i + f j + ∑ i ∈ range (r - 1 - j), f (j + 1 + i) := by
  have h : r = (j + 1) + (r - 1 - j) := by omega
  conv_lhs => rw [h]
  rw [Finset.sum_range_add, Finset.sum_range_succ]
end ClauseBound.ParityChecks.Num
