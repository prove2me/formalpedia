-- Prove2me | solution 1 for ClauseBound.Gen.End.alpha_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:13:10.679247+00:00
-- url     : https://prove2.me/submissions/9b3840e7-42ac-4589-ba0c-c56efd99ef42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Alg_Prog
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_End

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.End
namespace ClauseBound.Gen.End
theorem _root_.solution {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : 0 ≤ Real.logb 2 (1 / ρ) ∧ Real.logb 2 (1 / ρ) ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  constructor
  · apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hρ0]; linarith
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]
    linarith
end ClauseBound.Gen.End
