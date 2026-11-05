-- Prove2me | solution 1 for Eight.MulOut.getD_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:44.810433+00:00
-- url     : https://prove2.me/submissions/870c40e0-2f4c-4ca2-8bc6-9ebe5950beb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Eight_SecCrossing_MulOut

set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial
namespace Eight
namespace MulOut
theorem _root_.solution {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : (List.ofFn x).getD j false = bitAt x j := by
  unfold bitAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl
end MulOut
end Eight
