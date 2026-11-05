-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.sum_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:50:08.729204+00:00
-- url     : https://prove2.me/submissions/593e3ce5-722b-4094-992a-55aadb0c4ecd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_sum_marked
import Theorems.Thm_ClauseBound_Rec_CountRow_odd_eq
import Theorems.Thm_ClauseBound_Rec_CountRow_card_choices

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (n : ℕ) (hh : 1 ≤ h) : ((∑ β : Lab n, odd h β : ℕ) : ℝ) = 4 ^ n * mean n h := by
  have h1 := sum_marked (fun b : Fin (nblk n h) => BLab n h b) (oddSet n h)
  rw [card_choices hh, ← Equiv.sum_comp (split hh)] at h1
  push_cast at h1 ⊢
  rw [mean, ← h1]
  exact Finset.sum_congr rfl fun β _ => by rw [odd_eq hh]
end ClauseBound.Rec.CountRow
