-- Prove2me | solution 1 for Eight.Level.stPieces_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:06.04909+00:00
-- url     : https://prove2.me/submissions/2dcc89e7-66c5-4ed9-848d-216c62e47e1c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Pieces
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SingleBitPieces_Level_Pieces_sum_ofFn


set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset
namespace Eight.Level
theorem _root_.solution (hF : StFact)
    (ha_sum : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam, ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v)
    (ha_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam) : StPieces := by
  intro lam hlam
  refine ⟨ha_sum lam hlam, ?_⟩
  have hb : ∀ i, i < eightF.cnt 0 lam → _ := fun i hi => hF lam hlam i (Nat.lt_succ_iff.1 hi)
  refine ⟨Nat.succ_pos _, le_rfl, fun tr i hi x y u v => ?_, fun tr i _ => ?_, fun i hi x y u v => ?_, fun tr i hi x y θ => ?_, fun tr i hi x y θ => ?_⟩
  · cases tr
    · exact ((hb i hi).1 x y u v).trans
        (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (false, i, List.ofFn x, List.ofFn y, θ) * fBot (false, i, List.ofFn u, List.ofFn v, θ))
    · exact ((hb i hi).2.1 x u y v).trans
        (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (true, i, List.ofFn x, List.ofFn y, θ) * fBot (true, i, List.ofFn u, List.ofFn v, θ))
  · cases tr
    · exact (min_le_left _ _).trans_eq (by change 2 * lam = 2 * 1 * lam; rw [mul_one])
    · exact (min_le_left _ _).trans_eq (by change 2 * lam = 2 * 1 * lam; rw [mul_one])
  · exact ha_abs lam i hlam (Nat.lt_succ_iff.1 hi) x y u v
  · exact ((hb i hi).2.2 tr x y θ).1
  · exact ((hb i hi).2.2 tr x y θ).2
end Eight.Level
