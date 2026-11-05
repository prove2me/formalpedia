-- Prove2me | solution 1 for ClauseBound.Gen.Pick.g_le_K_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:14.879611+00:00
-- url     : https://prove2.me/submissions/7cac912b-71b1-43c4-9f8e-8afb7b79837f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_ClauseBound_Gen_Pick_K_succ

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
namespace ClauseBound.Gen.Pick
theorem _root_.solution (x₀ l : ℕ) : g x₀ l ≤ K x₀ (l + 1) := by
  rw [K_succ]; exact Nat.le_self_pow (by norm_num) _
end ClauseBound.Gen.Pick
