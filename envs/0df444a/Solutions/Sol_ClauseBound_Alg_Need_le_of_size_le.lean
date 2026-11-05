-- Prove2me | solution 1 for ClauseBound.Alg.Need.le_of_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:44.832291+00:00
-- url     : https://prove2.me/submissions/6ee50fee-51d3-4a27-8bfa-8f588143273a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_Need
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Need
open PaddedDescent.F
namespace ClauseBound.Alg.Need
theorem _root_.solution {x n F : ℕ} (h : 2 ^ n ≤ F) (hx : Nat.size x ≤ n) : x ≤ F :=
  (Nat.lt_size_self x).le.trans ((Nat.pow_le_pow_right (by norm_num) hx).trans h)
end ClauseBound.Alg.Need
