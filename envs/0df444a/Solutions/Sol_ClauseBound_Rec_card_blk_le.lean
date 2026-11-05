-- Prove2me | solution 1 for ClauseBound.Rec.card_blk_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:53.433267+00:00
-- url     : https://prove2.me/submissions/413572f0-7549-40a4-a072-e91e1aa1591d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_Blocks

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
variable {n h : ℕ}
namespace ClauseBound.Rec
theorem _root_.solution (hh : 1 ≤ h) (b : ℕ) : #(blk n h b) ≤ h := by
  have h1 : #(blk n h b) ≤ #(Ico (b * h) (b * h + h)) := by
    refine card_le_card_of_injOn (fun k => k.val) ?_ (fun _ _ _ _ e => Fin.ext e)
    intro k hk
    have hk' : k.val / h = b := by simpa [blk] using hk
    have h3 := Nat.div_add_mod k.val h
    have h4 := Nat.mod_lt k.val hh
    rw [hk', Nat.mul_comm] at h3
    simp only [coe_Ico, Set.mem_Ico]
    omega
  simpa using h1
end ClauseBound.Rec
