-- Prove2me | solution 1 for ExplicitCost.own_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:53.573393+00:00
-- url     : https://prove2.me/submissions/9d273047-ffc9-49de-8f19-6e320e527752

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Count
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountStep
import Theorems.Thm_ExplicitCost_own_le_aux

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines
namespace ExplicitCost
theorem _root_.solution {X T s u a κ q t : ℝ} (C : ℕ) (hX : 2 ≤ X) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ht : 1 ≤ t) (ha : 0 ≤ a) :
    a * (X ^ C * κ) + q + X ^ C + a * ((s * X ^ C * (u + 2) + s * X ^ C * t + 2) * T + 2) ≤
      a * ((κ + t * T * s * (u * X ^ (C + 3))) * X ^ C + 2 * X ^ C) + q + X ^ C := by
  have hX3 : (8 : ℝ) ≤ X ^ 3 := by
    have : (2 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
    linarith
  rw [pow_add]
  exact own_le_aux (one_le_pow₀ (by linarith)) hX3 hT hs hu ht ha
end ExplicitCost
