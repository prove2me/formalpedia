-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.mem_Dset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:46.825703+00:00
-- url     : https://prove2.me/submissions/0e297a5f-4257-498d-932a-4539b0bd0d5f

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
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution {e : ℕ} (he : e < q.m) : (⟨e, he⟩ : Fin q.m) ∈ Dset q.m e := by
  simp [Dset]
end ClauseBound.ParityChecks.Run
