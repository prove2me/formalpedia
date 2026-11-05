-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.countP_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:14.581211+00:00
-- url     : https://prove2.me/submissions/c7d45bca-cfbc-4f6e-bffb-2422869e3a68

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
theorem _root_.solution (x : ℕ) (Ls : List Chk) :
    (Ls.countP fun L => decide (x ∈ L)) = (Ls.map fun L => if x ∈ L then 1 else 0).sum := by
  induction Ls with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
    by_cases h : x ∈ a <;> simp [h, add_comm]
end ClauseBound.ParityChecks.Num
