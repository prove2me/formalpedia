-- Prove2me | solution 1 for ExplicitCost.cutsOK_piecesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:35:48.780659+00:00
-- url     : https://prove2.me/submissions/abb650dd-b56e-420d-acb3-e3406e505a23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
import Theorems.Thm_ExplicitCost_bot_piecesOf
import Theorems.Thm_ExplicitCost_card_I_pos
import Theorems.Thm_ExplicitCost_indexAt_mem
import Theorems.Thm_ExplicitCost_top_piecesOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_PaddedDescent_F_RebalF_cap_le
import Theorems.Thm_SingleBitPieces_Level_Presents_size_f
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) (pad : U) :
    CutsOK (piecesOf D c) pad 0 lam fun j => (D.fam lam).A (indexAt D lam j) where
  cnt_pos := card_I_pos hS.is hlam
  m_pos := le_rfl
  factors := fun tr i hi x y u v => by
    have hm := indexAt_mem D lam hi
    cases tr
    · refine (hS.is.row lam hlam _ hm x y u v).trans (Finset.sum_congr rfl fun θ hθ => ?_)
      have hl : θ.length = D.cap lam false (indexAt D lam i) := mem_words.1 hθ
      change _ = (piecesOf D c).top ((pad, false), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) * (piecesOf D c).bot ((pad, false), (0, i), (ClauseBound.Alg.bitsOf u, ClauseBound.Alg.bitsOf v, θ))
      rw [top_piecesOf, bot_piecesOf, if_pos hl, if_pos hl]
    · refine (hS.is.col lam hlam _ hm x u y v).trans (Finset.sum_congr rfl fun θ hθ => ?_)
      have hl : θ.length = D.cap lam true (indexAt D lam i) := mem_words.1 hθ
      change _ = (piecesOf D c).top ((pad, true), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) * (piecesOf D c).bot ((pad, true), (0, i), (ClauseBound.Alg.bitsOf u, ClauseBound.Alg.bitsOf v, θ))
      rw [top_piecesOf, bot_piecesOf, if_pos hl, if_pos hl]
  cap_le := fun tr i _ => by
    change D.cap lam tr (indexAt D lam i) ≤ 2 * 1 * lam
    have := hS.short lam tr (indexAt D lam i)
    omega
  abs_A := fun i hi x y u v => (hS.is.size_A lam hlam _ (indexAt_mem D lam hi) x y u v).le
  abs_top := fun tr i hi x y θ => by
    change |(piecesOf D c).top ((pad, tr), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ))| ≤ _
    rw [top_piecesOf]
    by_cases hθ : θ.length = D.cap lam tr (indexAt D lam i)
    · rw [if_pos hθ]
      exact (hS.is.size_f lam hlam _ (indexAt_mem D lam hi) tr false (x, y) θ (mem_words.2 hθ)).le
    · rw [if_neg hθ, abs_zero]
      positivity
  abs_bot := fun tr i hi x y θ => by
    change |(piecesOf D c).bot ((pad, tr), (0, i), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ))| ≤ _
    rw [bot_piecesOf]
    by_cases hθ : θ.length = D.cap lam tr (indexAt D lam i)
    · rw [if_pos hθ]
      exact (hS.is.size_f lam hlam _ (indexAt_mem D lam hi) tr true (x, y) θ (mem_words.2 hθ)).le
    · rw [if_neg hθ, abs_zero]
      positivity
end ExplicitCost
