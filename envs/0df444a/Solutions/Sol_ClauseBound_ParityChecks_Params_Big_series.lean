-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:48:44.751137+00:00
-- url     : https://prove2.me/submissions/9efd15b0-d73a-4865-82d3-f79041f0c338

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big___ge_9297678cfbb5
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_nb
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_pos
import Theorems.Thm_ClauseBound_ParityChecks_Params_series_real
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_ten_n_le

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
theorem _root_.solution (u : ℕ) (hu : u ≤ m) :
    |(1 - 2 * pr (nbOf n Δ)) ^ u - ∑ i ∈ range (i0Of n + 1), (-2 * pr (nbOf n Δ)) ^ i * (u.choose i : ℚ)| ≤ 2 / 2 ^ (10 * n) := by
  have h1 := series_real hu b.i0_pos (by have := b.two_le_nb; omega) (by have := b.ℓ_ge; omega : 1 ≤ ℓ - ℓ / 2) b.key
  have h2 : (1 / (2 : ℝ) ^ (ℓ - ℓ / 2)) ^ i0Of n ≤ 1 / 2 ^ (10 * n) := by
    rw [one_div_pow, ← pow_mul]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) b.ten_n_le)
  have h3 : ((|(1 - 2 * pr (nbOf n Δ)) ^ u - ∑ i ∈ range (i0Of n + 1), (-2 * pr (nbOf n Δ)) ^ i * (u.choose i : ℚ)| : ℚ) : ℝ) ≤
      ((2 / 2 ^ (10 * n) : ℚ) : ℝ) := by
    unfold pr
    push_cast
    calc _ ≤ 2 * (1 / (2 : ℝ) ^ (ℓ - ℓ / 2)) ^ i0Of n := h1
      _ ≤ 2 * (1 / 2 ^ (10 * n)) := by linarith
      _ = 2 / 2 ^ (10 * n) := by ring
  exact_mod_cast h3
end ClauseBound.ParityChecks.Params.Big
