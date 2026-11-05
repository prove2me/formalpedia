-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.inv_runTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:22:33.857926+00:00
-- url     : https://prove2.me/submissions/4fe5464c-ed85-436b-854d-1c464f7176eb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_step
import Theorems.Thm_ClauseBound_ParityChecks_Run_runTo_succ

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
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} (h : Inv q V ε Ls [] 0) :
    ∀ e ≤ q.m, Inv q V ε Ls (q.runTo orcA orcB Ls e) e := by
  intro e
  induction e with
  | zero => exact fun _ => h
  | succ e ih =>
    intro he
    rw [runTo_succ]
    exact (ih (by omega)).step H2 hq ho he
end ClauseBound.ParityChecks.Run
