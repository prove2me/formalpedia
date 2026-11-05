-- Prove2me | solution 1 for ClauseBound.Alg.Level.le_mul_div_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:19.189921+00:00
-- url     : https://prove2.me/submissions/4a5a96d8-61c6-467e-ba4a-76e24daf1c57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Level

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
namespace ClauseBound.Alg.Level
theorem _root_.solution (x : ℕ) {y : ℕ} (hy : 0 < y) : x ≤ y * (x / y + 1) :=
  (Nat.lt_mul_div_succ x hy).le
end ClauseBound.Alg.Level
