-- Prove2me | solution 1 for ClauseBound.Alg.Need.pow_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:45.979197+00:00
-- url     : https://prove2.me/submissions/7907dd0a-f36f-4b33-bf6d-c698255804d2

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
theorem _root_.solution {a n F : ℕ} (h : 2 ^ n ≤ F) (ha : a ≤ n) : 2 ^ a ≤ F :=
  (Nat.pow_le_pow_right (by norm_num) ha).trans h
end ClauseBound.Alg.Need
