-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.lowerOR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:54.244562+00:00
-- url     : https://prove2.me/submissions/b4659b94-925b-4839-9e08-0135b9482fbd

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
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_lowerO
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution {k K n s C₀ : ℕ} (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    (K : ℝ) * ((3 * K ^ 8 * K.size : ℕ) : ℝ) ≤ 3 * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1) : ℕ) : ℝ) ≤ ((3 * GO C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((K - 1) * lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) : ℕ) : ℝ) ≤
      ((55 + 354 * k + GO C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    ((3 * K ^ 8 * PbOL K n (2 ^ betaN k s) : ℕ) : ℝ) ≤ (GO C₀ : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((54 * K ^ 16 : ℕ) : ℝ) ≤ 54 * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (K : ℝ) ^ 2 ≤ ((Wof k K s : ℕ) : ℝ) * n ∧
    (K : ℝ) * ((C₀ : ℝ) * (K : ℝ) ^ 2 * ((5 * (17 * C₀ * K.size) + 16 : ℕ) : ℝ)) ≤ ((C₀ * (85 * C₀ + 16) : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * ((3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) : ℕ) : ℝ) ≤ ((27 * (4 + 17 * C₀) : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) ∧
    (K : ℝ) * (((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) : ℕ) : ℝ) ≤
      ((17 + 51 * C₀ : ℕ) : ℝ) * (((Wof k K s : ℕ) : ℝ) * n) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := lowerO (k := k) (s := s) (C₀ := C₀) hK hn17 hlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast o1
  · exact_mod_cast o2
  · exact_mod_cast o3
  · exact_mod_cast o4
  · exact_mod_cast o5
  · exact_mod_cast o6
  · exact_mod_cast o7
  · exact_mod_cast o8
  · exact_mod_cast o9
end ClauseBound.ParityChecks.ArithOL
