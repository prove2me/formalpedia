-- Prove2me | solution 1 for ClauseBound.Rec.two_mul_mu_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:19.141497+00:00
-- url     : https://prove2.me/submissions/9ade678d-fb42-4de4-846d-285c77d4308b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_mu_le_mean
import Theorems.Thm_ClauseBound_Rec_CountRow_mean_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) : 2 * mu n h ≤ nblk n h := by
  have h1 := (mu_le_mean n hh).trans (mean_le n h)
  have h2 : ((2 * mu n h : ℕ) : ℝ) ≤ (nblk n h : ℝ) := by push_cast; linarith
  exact_mod_cast h2
end ClauseBound.Rec
