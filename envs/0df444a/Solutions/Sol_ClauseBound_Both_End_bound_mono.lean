-- Prove2me | solution 1 for ClauseBound.Both.End.bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:30.483517+00:00
-- url     : https://prove2.me/submissions/19a72749-4820-4b2b-8960-3685a4058efe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_ClauseBound_Both_End

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Both ClauseBound.Both.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
namespace ClauseBound.Both.End
theorem _root_.solution {r : ℕ → ℝ} {D D' : ℕ} (h : D ≤ D') (k m : ℕ) (hr : 0 ≤ r m) : SatM.bound r D k m ≤ SatM.bound r D' k m := by
  unfold SatM.bound
  have hD : (D : ℝ) ≤ D' := by exact_mod_cast h
  refine Nat.floor_le_floor (mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by positivity) (by positivity))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (by positivity)) hr
end ClauseBound.Both.End
