-- Prove2me | solution 1 for Eight.Level.level_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:25:38.391704+00:00
-- url     : https://prove2.me/submissions/2af2c75f-87e5-475a-9362-97f5d2bb589e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Arith
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Arith
import Theorems.Thm_SingleBitPieces_Level_level_size


set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork
open Arith
namespace Eight.Level
theorem _root_.solution (g a A Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M P B' : ℕ, 1 ≤ lam → M ≤ 2 * Rn * lam → P ≤ g ^ 3 * lam →
    B' ≤ (g + 2 * g ^ 2) * (B + lam) →
    2 * sc + 2 * M + g * (P + B') + g * g * B' + 20 + a * (sc + B + lam) ^ a + A * (sc + (M + 1) + P + B') ^ A
      ≤ A2 * (sc + B + lam) ^ A2 :=
  SingleBitPieces.Level.level_size g a A Rn
end Eight.Level
