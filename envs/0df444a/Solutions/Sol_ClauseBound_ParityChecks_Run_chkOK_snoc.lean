-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.chkOK_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:41.220203+00:00
-- url     : https://prove2.me/submissions/191c08fc-fc5a-4923-9db0-09d88546c99f

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
theorem _root_.solution {e : ℕ} {L : Chk} (hL : ChkOK e L) : ChkOK (e + 1) (L ++ [e]) := by
  refine ⟨List.Nodup.append hL.1 (List.nodup_singleton e) ?_, fun x hx => ?_⟩
  · intro a ha hb
    have h1 := hL.2 a ha
    have h2 : a = e := by simpa using hb
    omega
  · rcases List.mem_append.1 hx with h | h
    · exact (hL.2 x h).trans (Nat.lt_succ_self e)
    · have h2 : x = e := by simpa using h
      omega
end ClauseBound.ParityChecks.Run
