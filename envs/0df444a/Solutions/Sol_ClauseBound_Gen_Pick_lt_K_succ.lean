-- Prove2me | solution 1 for ClauseBound.Gen.Pick.lt_K_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:07.767526+00:00
-- url     : https://prove2.me/submissions/a768dc76-202c-43f7-b5e5-91fb74431ca0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_ClauseBound_Gen_Pick_g_le_K_succ
import Theorems.Thm_ClauseBound_Gen_Pick_pow_le_g
import Theorems.Thm_ClauseBound_Gen_Pick_two_pow_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
namespace ClauseBound.Gen.Pick
theorem _root_.solution (x₀ l : ℕ) : l < K x₀ (l + 1) :=
  Nat.lt_two_pow_self.trans_le ((two_pow_le x₀ l).trans ((pow_le_g x₀ l).trans (g_le_K_succ x₀ l)))
end ClauseBound.Gen.Pick
