-- Prove2me | solution 1 for ClauseBound.Alg.Descend.fitsG_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:49:26.673797+00:00
-- url     : https://prove2.me/submissions/7c7b93a8-46a3-47bd-863c-79086b6c2d32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists
namespace ClauseBound.Alg.Descend
theorem _root_.solution {P : PiecesF} {F : ℕ} : ∀ {sched : List Step} {Kup lam B cnt z : ℕ}, FitsG P F Kup lam B cnt z sched →
    cnt * instLen Kup lam B + 8 * z + 4 * lam + 40 ≤ F
  | [], _, _, _, _, _, h => h.1
  | _ :: _, _, _, _, _, _, h => h.1
end ClauseBound.Alg.Descend
