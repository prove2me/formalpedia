-- Prove2me | solution 1 for Eight.Level.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:39:04.747746+00:00
-- url     : https://prove2.me/submissions/fd111449-83ae-41a3-8d76-bb4772a76206

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Eight_SecPseudocode_Levels
import Theorems.Thm_Eight_Level_levelE_tendsto
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_lt_levelK


set_option autoImplicit false
section
section
open Eight Eight.Level
open Paper SingleBitPieces.SecPseudocode_Levels
namespace Eight.Level
theorem _root_.solution {η : ℝ} (hη : 0 < η) (K₀ : ℕ) : ∃ ℓ, K₀ ≤ levelK ℓ ∧ levelE ℓ ≤ η := by
  obtain ⟨ℓ₁, h1⟩ := Filter.eventually_atTop.1 (levelE_tendsto.eventually_le_const hη)
  exact ⟨max ℓ₁ K₀, (le_max_right _ _).trans (lt_levelK _).le, h1 _ (le_max_left _ _)⟩
end Eight.Level
