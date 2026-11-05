-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.chkOK_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:29.447196+00:00
-- url     : https://prove2.me/submissions/e63653ac-92d2-4910-9f9e-085ff1c343f7

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
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution {e e' : ℕ} (h : e ≤ e') {L : Chk} (hL : ChkOK e L) : ChkOK e' L := ⟨hL.1, fun x hx => (hL.2 x hx).trans_le h⟩
end ClauseBound.ParityChecks.Run
