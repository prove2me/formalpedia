-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.Dset_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:49.341931+00:00
-- url     : https://prove2.me/submissions/ed8e447f-a017-4efe-97ed-d7084642d8e0

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
theorem _root_.solution {e : ℕ} (he : e < q.m) : Dset q.m (e + 1) = (Dset q.m e).erase ⟨e, he⟩ := by
  ext x
  simp only [Dset, mem_filter, mem_univ, true_and, mem_erase, ne_eq, Fin.ext_iff]
  omega
end ClauseBound.ParityChecks.Run
