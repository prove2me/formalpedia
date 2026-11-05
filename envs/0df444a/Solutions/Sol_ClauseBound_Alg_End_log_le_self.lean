-- Prove2me | solution 1 for ClauseBound.Alg.End.log_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:08:38.762448+00:00
-- url     : https://prove2.me/submissions/558d56ee-32bc-477f-b56a-805f2915a694

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat
namespace ClauseBound.Alg.End
theorem _root_.solution (m : ℕ) : Real.logb 2 ((m : ℝ) + 2) ≤ (m : ℝ) + 2 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  have h : ((m + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 2 : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self (n := m + 2)).le
  have e : (2 : ℝ) ^ ((m : ℝ) + 2) = (2 : ℝ) ^ (m + 2 : ℕ) := by rw [← Real.rpow_natCast]; push_cast; rfl
  rw [e]; exact_mod_cast h
end ClauseBound.Alg.End
