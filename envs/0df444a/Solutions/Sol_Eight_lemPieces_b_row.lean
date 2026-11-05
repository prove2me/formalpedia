-- Prove2me | solution 1 for Eight.lemPieces_b_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:09:26.431653+00:00
-- url     : https://prove2.me/submissions/f473555c-1265-48ec-b30c-574dc43b2943

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact

set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
namespace Eight
theorem _root_.solution (h : StFact) (lam i : ℕ) (hlam : 1 ≤ lam) (hi : i ≤ tOf lam) : FactorsLe (Pieces.rowwise (A lam i)) (crow lam i) (2 ^ tOf lam) :=
  ⟨fun p θ => fTop (false, i, List.ofFn p.1, List.ofFn p.2, List.ofFn θ), fun q θ => fBot (false, i, List.ofFn q.1, List.ofFn q.2, List.ofFn θ),
    fun p q => (h lam hlam i hi).1 p.1 p.2 q.1 q.2, fun p _ => ((h lam hlam i hi).2.2 false p.1 p.2 _).1, fun q _ => ((h lam hlam i hi).2.2 false q.1 q.2 _).2⟩
end Eight
