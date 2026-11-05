-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.drift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:47:00.724482+00:00
-- url     : https://prove2.me/submissions/633ef6e5-c958-4547-89d8-9c1ad77d9bbb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_beta0
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_two___le_d18f4ddaa33d
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_n_big
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LDt_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_r_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta0_le_four

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : (2 / 2 ^ (10 * n) : ℚ) * (2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) * (m * rOf n (beta0 m (nbOf n Δ))) < 1 / 4 := by
  have h1 : m.choose (nbOf n Δ + 1) ≤ 2 ^ (4 * n) :=
    le_trans (choose_le_beta0 _ _) (Nat.pow_le_pow_right (by norm_num) b.beta0_le_four)
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have hΔ : Δ ≤ 2 ^ n := by
    have h2 : 2 ^ LD Δ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := b.LDt_le; have := b.n_big; omega)
    have := two_Δ_le Δ
    omega
  have h64 : 64 ≤ 2 ^ n := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := b.n_big; omega)
  have h3 : 8 * (2 ^ n * m.choose (nbOf n Δ + 1)) * (m * rOf n (beta0 m (nbOf n Δ))) < 2 ^ (10 * n) := by
    calc 8 * (2 ^ n * m.choose (nbOf n Δ + 1)) * (m * rOf n (beta0 m (nbOf n Δ)))
        ≤ 8 * (2 ^ n * 2 ^ (4 * n)) * (2 ^ n * 2 ^ n * (6 * 2 ^ n)) := by
          have := b.r_le
          have hm : m ≤ 2 ^ n * 2 ^ n := le_trans b.hm (Nat.mul_le_mul hΔ hn.le)
          have hr : rOf n (beta0 m (nbOf n Δ)) ≤ 6 * 2 ^ n := by omega
          gcongr
      _ = 48 * 2 ^ (8 * n) := by
          rw [show 8 * n = n + 4 * n + n + n + n by ring, pow_add, pow_add, pow_add, pow_add]; ring
      _ < 64 * 2 ^ (8 * n) := by
          have : 0 < 2 ^ (8 * n) := by positivity
          omega
      _ ≤ 2 ^ n * 2 ^ n * 2 ^ (8 * n) := by
          have : 64 ≤ 2 ^ n * 2 ^ n := le_trans h64 (Nat.le_mul_of_pos_left _ (by positivity))
          gcongr
      _ = 2 ^ (10 * n) := by
          rw [show 10 * n = n + n + 8 * n by ring, pow_add, pow_add]
  have h4 : (8 : ℚ) * ((2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) : ℚ) * ((m : ℚ) * (rOf n (beta0 m (nbOf n Δ)) : ℚ)) < 2 ^ (10 * n) := by
    exact_mod_cast h3
  have hP : (0 : ℚ) < 2 ^ (10 * n) := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hP]
  linarith
end ClauseBound.ParityChecks.Params.Big
