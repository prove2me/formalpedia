-- Prove2me | solution 1 for ClauseBound.Alg.Need.stNeedG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:51:40.737503+00:00
-- url     : https://prove2.me/submissions/4c37c6b7-bf05-4034-a769-b0a6c852bcbc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_Need
import Theorems.Thm_ClauseBound_Alg_Need_fitsG_of_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Need
open PaddedDescent.F
namespace ClauseBound.Alg.Need
theorem _root_.solution (P : PiecesF) : StNeedG P := fun _ Kup lam B cnt z sched h => fitsG_of_le P h sched Kup lam B cnt z le_rfl
end ClauseBound.Alg.Need
