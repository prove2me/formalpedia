-- Prove2me | solution 1 for ClauseBound.ParityChecks.small_parOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:38:18.515095+00:00
-- url     : https://prove2.me/submissions/c02e9c4d-2b67-4e32-8ef9-4382b60f48c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_beta0
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_beta1

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
namespace ClauseBound.ParityChecks
theorem _root_.solution (n Δ m : ℕ) : ∀ i ≤ (parOf n Δ m).i₀, 2 ^ n * m.choose ((parOf n Δ m).nb + 1) * m.choose i ≤ 2 ^ ((parOf n Δ m).β - 2) := by
  intro i hi
  show 2 ^ n * m.choose (nbOf n Δ + 1) * m.choose i ≤ 2 ^ (n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 - 2)
  rw [Nat.add_sub_cancel, pow_add, pow_add]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (choose_le_beta0 _ _)) (choose_le_beta1 _ _ _ hi)
end ClauseBound.ParityChecks
