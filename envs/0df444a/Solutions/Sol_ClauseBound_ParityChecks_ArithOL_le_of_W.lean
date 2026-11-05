-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.le_of_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:44.849624+00:00
-- url     : https://prove2.me/submissions/aa689417-dc15-4423-a5b6-cb96e399c495

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution {k K n s A₁ : ℕ} {e : ℝ} (hKn : K ≤ n) (he0 : 0 ≤ e) (hnW : n ≤ Wof k K s)
    (hM : ((Wof k K s : ℕ) : ℝ) ≤ (A₁ : ℝ) * K * e) : (n : ℝ) ≤ (A₁ : ℝ) * ((n : ℝ) * e) := by
  have hKr : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hKn
  calc (n : ℝ) ≤ ((Wof k K s : ℕ) : ℝ) := by exact_mod_cast hnW
    _ ≤ (A₁ : ℝ) * K * e := hM
    _ ≤ (A₁ : ℝ) * n * e := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKr (Nat.cast_nonneg _)) he0
    _ = (A₁ : ℝ) * ((n : ℝ) * e) := by ring
end ClauseBound.ParityChecks.ArithOL
