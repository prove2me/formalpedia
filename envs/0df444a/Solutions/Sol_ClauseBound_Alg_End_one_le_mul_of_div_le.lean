-- Prove2me | solution 1 for ClauseBound.Alg.End.one_le_mul_of_div_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:47:39.087182+00:00
-- url     : https://prove2.me/submissions/3b10e55e-0a00-4969-b1e9-d56c8747ebbb

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
theorem _root_.solution {c : ℕ} {y r : ℝ} (hc : 1 ≤ c) (hy : 1 ≤ y) (h : 1 / ((c : ℝ) * y ^ c) ≤ r) : 1 ≤ (c : ℝ) * y ^ c * r := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hp : 0 < (c : ℝ) * y ^ c := by positivity
  rw [div_le_iff₀ hp] at h
  linarith
end ClauseBound.Alg.End
