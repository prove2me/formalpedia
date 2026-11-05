-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.num_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:44.911563+00:00
-- url     : https://prove2.me/submissions/11e40730-ccb8-4caf-afcb-7c6d347bf82c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (A : ℤ) {B B' : ℕ → ℤ} (h : ∀ i ≤ q.i₀, B i = B' i) (Ls : List Chk) (cur : Chk) (e : ℕ) : q.num A B Ls cur e = q.num A B' Ls cur e := by
  have h1 : q.numP A B = q.numP A B' := by
    unfold Par.numP
    congr 2
    exact List.map_congr_left fun i hi => by rw [h i (Nat.lt_succ_iff.1 (List.mem_range.1 hi))]
  unfold Par.num
  rw [h1]
end ClauseBound.ParityChecks.Run
