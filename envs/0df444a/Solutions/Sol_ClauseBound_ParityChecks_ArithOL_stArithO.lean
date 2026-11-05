-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.stArithO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:47:50.98013+00:00
-- url     : https://prove2.me/submissions/79819f84-ec22-4afa-952e-16fdb4a54f90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_planAtO_le
import Theorems.Thm_ClauseBound_TopN_Arith_eq_replicate
import Theorems.Thm_ClauseBound_TopN_Arith_master
import Theorems.Thm_ClauseBound_TopN_Arith_root17_spec
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution : StArithO := by
  intro Idx _ S e C₀ Q hS slU C k hk h1 h2
  refine ⟨cO k C C₀, fun n₀ => ⟨(354 * k * ckN k + ccO k C₀ * A1 k C C₀ + 1) + 2 ^ s0K k + A1 k C C₀ + n₀ ^ C₀, fun n hn => ?_⟩⟩
  obtain ⟨hr1, hr2⟩ := root17_spec n
  have hK0 : S.K (Q.idx 0) ≤ (root17 n).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
    exact absurd (h'.trans hn) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root17 n)
  have hidx := Q.pick_idx (root17 n)
  have hu := eq_replicate (Q.pick (root17 n)).1
  obtain ⟨l, hl⟩ : ∃ l, l = (Q.pick (root17 n)).1.length := ⟨_, rfl⟩
  rw [← hl] at hu hidx hmax ⊢
  rw [hidx] at hle ⊢
  rw [hu]
  have g1 := h1 l
  have g2 := h2 l
  obtain ⟨s, hs⟩ : ∃ s, s = (slU (List.replicate l ())).length := ⟨_, rfl⟩
  rw [← hs] at g1 g2 ⊢
  have hK2 := Q.K_two l
  have hn17 : S.K (Q.idx l) ^ 17 ≤ n := (Nat.pow_le_pow_left hle 17).trans hr1
  have hlt : n < S.K (Q.idx l) ^ (17 * C₀) := by
    calc n < ((root17 n).length + 1) ^ 17 := hr2
      _ ≤ (S.K (Q.idx l) ^ C₀) ^ 17 := Nat.pow_le_pow_left ((Nat.succ_le_of_lt hmax).trans (Q.K_le _)) 17
      _ = S.K (Q.idx l) ^ (17 * C₀) := by rw [← pow_mul, mul_comm]
  have hM := master (k := k) hK2 (Q.e_ge l) g2
  have h := planAtO_le hS (Q.idx l) (k := k) (s := s) (n₀ := n₀) hK2 hn17 hlt (Q.e_le l) g1 (Q.e_ge l) g2 hM (Q.rate l)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]
  exact h
end ClauseBound.ParityChecks.ArithOL
