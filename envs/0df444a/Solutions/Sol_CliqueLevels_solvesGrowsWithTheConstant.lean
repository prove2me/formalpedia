-- Prove2me | solution 1 for CliqueLevels.solvesGrowsWithTheConstant
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:01:18.276046+00:00
-- url     : https://prove2.me/submissions/8c4408f4-e7b5-4398-b15b-272e9eb578fb

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
set_option autoImplicit false
section
section
open CliqueLevels
open Groundwork Printed Proof

namespace CliqueLevels.Proof

/-- The polynomial factor grows with the constant. -/
theorem factor_mono {K C₀ C₁ lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (h : C₀ ≤ C₁) :
    factor K C₀ lam B ≤ factor K C₁ lam B := by
  unfold factor
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl' : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  exact pow_le_pow_right₀ (by nlinarith) (Nat.mul_le_mul_right _ h)

/-- The bound grows with the constant. -/
theorem bound_mono {e : ℝ} {K C₀ C₁ lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (h : C₀ ≤ C₁) :
    bound e K C₀ lam B ≤ bound e K C₁ lam B :=
  mul_le_mul_of_nonneg_left (factor_mono hK hl h) (by positivity)

end CliqueLevels.Proof

theorem solution : SolvesGrowsWithTheConstant := by
  intro M K e C₀ C₁ hK h
  refine ⟨fun hS l lam B W hl hB hW => ?_, fun hS l lam B W hl hB hW => ?_⟩
  · obtain ⟨T, S, hr, hT, hSz⟩ := hS l lam B W hl hB hW
    exact ⟨T, S, hr, hT.trans (bound_mono (hK l) hl h), hSz.trans (bound_mono (hK l) hl h)⟩
  · obtain ⟨T, S, hr, hT, hSz⟩ := hS l lam B W hl hB hW
    exact ⟨T, S, hr, hT.trans (bound_mono (hK l) hl h), hSz.trans (factor_mono (hK l) hl h)⟩
