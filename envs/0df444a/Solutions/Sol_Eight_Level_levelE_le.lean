-- Prove2me | solution 1 for Eight.Level.levelE_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:25:35.036099+00:00
-- url     : https://prove2.me/submissions/ab5fcf14-452f-4d25-9386-09355fcaa5a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Eight_SecPseudocode_Levels
import Theorems.Thm_Eight_Level_levelE_le_sub
import Theorems.Thm_SingleBitPieces_SecPseudocode_Levels_levelK_pos


set_option autoImplicit false
section
section
open Eight Eight.Level
open Paper SingleBitPieces.SecPseudocode_Levels
namespace Eight.Level
theorem _root_.solution (ℓ : ℕ) : levelE ℓ ≤ 0.56 * rho ^ ℓ := by
  have h1 := levelE_le_sub ℓ
  have h2 : 0 ≤ 3.8 / (levelK ℓ : ℝ) := by have := levelK_pos ℓ; positivity
  linarith
end Eight.Level
