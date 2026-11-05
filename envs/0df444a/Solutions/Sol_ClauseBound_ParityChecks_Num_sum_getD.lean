-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.sum_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:18.485753+00:00
-- url     : https://prove2.me/submissions/af79be06-47c5-4f85-aca1-9e987ef5aa5b

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
theorem _root_.solution {M : Type} [AddCommMonoid M] (g : Chk → M) (Ls t : List Chk) :
    ∑ i ∈ range Ls.length, g ((Ls ++ t).getD i []) = (Ls.map g).sum := by
  induction Ls with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    congr 1
end ClauseBound.ParityChecks.Num
