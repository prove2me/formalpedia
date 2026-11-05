-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.Inv.tent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:16:46.92581+00:00
-- url     : https://prove2.me/submissions/02b1ba83-7057-4f7a-b736-601069e99003

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_lam_putIn
import Theorems.Thm_ClauseBound_ParityChecks_Run_tent_out
import Theorems.Thm_ClauseBound_ParityChecks_Run_tent_in
import Theorems.Thm_ClauseBound_ParityChecks_Run_bd_of_lt_one
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_lt_one

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
namespace Inv
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e) (he : e < q.m) :
    Tent q (lam q.m (Ls ++ [cur ++ [e]])) ∧ Tent q (lam q.m (Ls ++ [cur])) := by
  have hb := bd_of_lt_one H2 hq h.lt h.okc (h.lt_one hq)
  rw [lam_putIn Ls cur he]
  exact ⟨tent_in hb _ _, tent_out hb⟩
end Inv
end ClauseBound.ParityChecks.Run
