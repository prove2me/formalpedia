-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.prod_sg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:45:02.93987+00:00
-- url     : https://prove2.me/submissions/82401fc8-cfd8-435e-a000-46e6866f1f89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
namespace ClauseBound.Rec.CountRow
theorem _root_.solution {ι : Type} [Fintype ι] (γ : ι → Bool × Bool) :
    ∏ k, sg (γ k) = if Odd #{k | γ k = (true, true)} then -1 else 1 := by
  have h : ∏ k, sg (γ k) = (-1) ^ #{k | γ k = (true, true)} := by
    unfold sg
    rw [Finset.prod_ite]
    simp
  rw [h]
  split_ifs with ho
  · exact ho.neg_one_pow
  · exact (Nat.not_odd_iff_even.1 ho).neg_one_pow
end ClauseBound.Rec.CountRow
