-- Prove2me | solution 1 for ClauseBound.Rec.mu_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:30.350472+00:00
-- url     : https://prove2.me/submissions/e2c1abfd-fd94-4aca-bebd-347a7cbf8fe9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_mu_le_mean
import Theorems.Thm_ClauseBound_Rec_CountRow_mean_lt
import Theorems.Thm_ClauseBound_Rec_CountRow_mean_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) :
    mu n h = (∑ b ∈ range (nblk n h), (2 ^ #(blk n h b) - 1) * 2 ^ (h - #(blk n h b))) / 2 ^ (h + 1) := by
  have h1 := mu_le_mean n hh
  have h2 := mean_lt n hh
  rw [mean_eq n hh] at h1 h2
  have h3 := (Nat.floor_eq_iff (by positivity)).2 ⟨h1, h2⟩
  rw [Nat.floor_div_eq_div] at h3
  exact h3.symm
end ClauseBound.Rec
