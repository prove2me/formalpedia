-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.tent_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:14:56.01639+00:00
-- url     : https://prove2.me/submissions/8418317b-e96e-4cc1-a425-3edbec182a5c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_lt_two_mul

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution {Λ : ℕ → Finset (Fin q.m)} (h : Bd q Λ) : Tent q Λ where
  inc := h.inc.trans (lt_add_one _)
  row j' hj' := lt_two_mul (by positivity) (h.row j' hj')
  col x := lt_two_mul (by positivity) (h.col x)
end ClauseBound.ParityChecks.Run
