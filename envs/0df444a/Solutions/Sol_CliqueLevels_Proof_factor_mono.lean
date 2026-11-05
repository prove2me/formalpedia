-- Prove2me | solution 1 for CliqueLevels.Proof.factor_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:38:28.944211+00:00
-- url     : https://prove2.me/submissions/0d1e9bae-6958-4e61-83b5-0aa6438cc2f5

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
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed
namespace CliqueLevels.Proof
theorem _root_.solution {K C₀ C₁ lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (h : C₀ ≤ C₁) : factor K C₀ lam B ≤ factor K C₁ lam B := by
  unfold factor
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl' : (1 : ℝ) ≤ lam := by exact_mod_cast hl
  have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  exact pow_le_pow_right₀ (by nlinarith) (Nat.mul_le_mul_right _ h)
end CliqueLevels.Proof
