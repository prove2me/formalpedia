-- Prove2me | solution 1 for Eight.Level.levelE_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:32:47.681339+00:00
-- url     : https://prove2.me/submissions/36a49362-7777-4718-94d6-57b4d564dbef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Eight_SecPseudocode_Levels
import Theorems.Thm_Eight_Level_rho_pos
import Theorems.Thm_Eight_Level_rho_lt_one
import Theorems.Thm_Eight_Level_levelE_nonneg
import Theorems.Thm_Eight_Level_levelE_le

set_option autoImplicit false
section
section
open Eight Eight.Level
open Paper SingleBitPieces.SecPseudocode_Levels
namespace Eight.Level
theorem _root_.solution : Filter.Tendsto levelE Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun ℓ : ℕ => 0.56 * rho ^ ℓ) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul (0.56 : ℝ)
    rwa [mul_zero] at h
  exact squeeze_zero levelE_nonneg levelE_le h1
end Eight.Level
