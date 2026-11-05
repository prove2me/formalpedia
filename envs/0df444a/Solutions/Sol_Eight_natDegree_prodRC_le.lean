-- Prove2me | solution 1 for Eight.natDegree_prodRC_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:49:55.047594+00:00
-- url     : https://prove2.me/submissions/9586dc39-6aa6-4962-9941-3fbe6a14cd40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
import Theorems.Thm_Eight_natDegree_prod_linear_le

set_option autoImplicit false
section
section
open Eight
open Finset Polynomial
namespace Eight
theorem _root_.solution {lam : ℕ} (x y u v : Pieces.Bits lam) : (prodRC x y u v).natDegree ≤ tOf lam := by
  simpa [prodRC] using natDegree_prod_linear_le (range (tOf lam)) (fun s => Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s))
    (fun s => Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s))
end Eight
