-- Prove2me | solution 1 for Eight.Fact.abs_prodL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:18:32.75267+00:00
-- url     : https://prove2.me/submissions/891317c8-7203-4fd3-a85c-127cacb6e140

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_PaddedDescent_F_prodL_eq


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact
namespace Eight.Fact
theorem _root_.solution {t : ℕ} {f : ℕ → ℤ} (h : ∀ s, |f s| ≤ 1) : |prodL t f| ≤ 1 := by
  rw [prodL_eq, abs_prod]
  exact prod_le_one (fun _ _ => abs_nonneg _) fun s _ => h s
end Eight.Fact
