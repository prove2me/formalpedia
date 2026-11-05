-- Prove2me | solution 1 for Eight.A_eq_sum_subsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:54.287977+00:00
-- url     : https://prove2.me/submissions/665dbccc-401e-498d-b56b-db6eb04873df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_coeff_prod_linear

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution (lam i : ℕ) (x y u v : Pieces.Bits lam) :
    A lam i x y u v = ∑ Q ∈ (Finset.range (tOf lam)).powersetCard i, ∏ s ∈ Finset.range (tOf lam),
      if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) :=
  coeff_prod_linear (range (tOf lam)) (fun s => Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s))
    (fun s => Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) i
end Eight
