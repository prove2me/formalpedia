-- Prove2me | solution 1 for CliqueLevels.Proof.bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:53.318049+00:00
-- url     : https://prove2.me/submissions/1d37d64d-c58e-4774-b52c-b55691877b85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Closure_Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_GenLevels
import Theorems.Thm_CliqueLevels_Proof_factor_mono

set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution {e : ℝ} {K C₀ C₁ lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (h : C₀ ≤ C₁) : bound e K C₀ lam B ≤ bound e K C₁ lam B :=
  mul_le_mul_of_nonneg_left (factor_mono hK hl h) (by positivity)
end CliqueLevels.Proof
