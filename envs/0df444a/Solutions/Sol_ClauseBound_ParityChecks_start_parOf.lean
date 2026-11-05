-- Prove2me | solution 1 for ClauseBound.ParityChecks.start_parOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:38:45.829952+00:00
-- url     : https://prove2.me/submissions/3b377f82-61b8-4425-a373-97384586f328

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_beta0
import Theorems.Thm_ClauseBound_ParityChecks_Params_two_pow_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
namespace ClauseBound.ParityChecks
theorem _root_.solution (n Δ m : ℕ) : (5 / 8 : ℚ) ^ (parOf n Δ m).r * (2 ^ n * m.choose ((parOf n Δ m).nb + 1) : ℕ) ≤ 1 / 8 := by
  show (5 / 8 : ℚ) ^ rOf n (beta0 m (nbOf n Δ)) * (2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) ≤ 1 / 8
  have h1 : ((2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) : ℚ) ≤ 2 ^ (n + beta0 m (nbOf n Δ)) := by
    have : 2 ^ n * m.choose (nbOf n Δ + 1) ≤ 2 ^ (n + beta0 m (nbOf n Δ)) := by
      rw [pow_add]; exact Nat.mul_le_mul_left _ (choose_le_beta0 _ _)
    exact_mod_cast this
  have h2 := two_pow_le (n + beta0 m (nbOf n Δ) + 3) (rOf n (beta0 m (nbOf n Δ))) (by unfold rOf; omega)
  generalize rOf n (beta0 m (nbOf n Δ)) = r at *
  generalize n + beta0 m (nbOf n Δ) = X at *
  have h3 : (5 / 8 : ℚ) ^ r * (8 / 5) ^ r = 1 := by rw [← mul_pow]; norm_num
  have h4 : (0 : ℚ) < (5 / 8) ^ r := by positivity
  rw [pow_add] at h2
  calc (5 / 8 : ℚ) ^ r * ((2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) : ℚ) ≤ (5 / 8) ^ r * 2 ^ X := mul_le_mul_of_nonneg_left h1 h4.le
    _ = 1 / 8 * ((5 / 8) ^ r * (2 ^ X * 2 ^ 3)) := by ring
    _ ≤ 1 / 8 * ((5 / 8) ^ r * (8 / 5) ^ r) := by gcongr
    _ = 1 / 8 := by rw [h3]; ring
end ClauseBound.ParityChecks
