-- Prove2me | solution 1 for ClauseBound.Gen.Chain.price_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:24.334693+00:00
-- url     : https://prove2.me/submissions/ca2254d8-daea-40e8-87b1-9b41877664b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Theorems.Thm_Groundwork_Grid_digit_le
import Theorems.Thm_Groundwork_Prog_digit_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Levels.Gen
namespace ClauseBound.Gen.Chain
theorem _root_.solution (P : PiecesF) (p d h lam y : ℕ) (hc : 1 ≤ P.cnt h lam) :
    priceG P p d false h lam y + priceG P p d true h lam y ≤ 2 * (nRectG p d * capSum P h lam) := by
  unfold priceG
  rw [← Nat.mul_add, ← Finset.sum_add_distrib]
  refine Nat.mul_le_mul_left 2 ?_
  calc ∑ q ∈ Finset.range (nRectG p d), (P.cap false h lam (digit (P.cnt h lam - 1) y q) + P.cap true h lam (digit (P.cnt h lam - 1) y q))
      ≤ ∑ _q ∈ Finset.range (nRectG p d), capSum P h lam := by
        refine Finset.sum_le_sum fun q _ => ?_
        have hd : digit (P.cnt h lam - 1) y q ∈ Finset.range (P.cnt h lam) := by
          have := digit_le (P.cnt h lam - 1) y q
          rw [Finset.mem_range]; omega
        exact Finset.le_sup (f := fun i => P.cap false h lam i + P.cap true h lam i) hd
    _ = nRectG p d * capSum P h lam := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
end ClauseBound.Gen.Chain
