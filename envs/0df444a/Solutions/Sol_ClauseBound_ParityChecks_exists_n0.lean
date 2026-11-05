-- Prove2me | solution 1 for ClauseBound.ParityChecks.exists_n0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:54:15.478536+00:00
-- url     : https://prove2.me/submissions/0f69e4cf-3c4e-433c-b638-c0dab92ed4e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_mul_clog_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_nb_mul_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_lt_two_mul
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_r_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta0_le_four
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_hyp

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
namespace ClauseBound.ParityChecks
theorem _root_.solution (c : ℕ) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ Δ m : ℕ, 2 ≤ Δ → Δ ≤ (Nat.log 2 n + 1) ^ c → nbOf n Δ < m → m ≤ Δ * n →
    Hyp (parOf n Δ m) (2 ^ n) (2 / 2 ^ (10 * n)) ∧ (parOf n Δ m).r ≤ 6 * n ∧ (parOf n Δ m).β ≤ 5 * n ∧
      beta0 m (nbOf n Δ) ≤ 4 * n ∧ nbOf n Δ * LD Δ ≤ n ∧ n < 2 * (nbOf n Δ * LD Δ) := by
  refine ⟨2 ^ (2 * (84 * (c + 1)) ^ 2), fun n hn Δ m hΔ2 hΔ hnb hm => ?_⟩
  have hℓ : 2 * (84 * (c + 1)) ^ 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have b : Big c n Δ m (Nat.log 2 n) (Nat.clog 2 (Nat.log 2 n + 1)) :=
    { hℓ := rfl
      ht := rfl
      hℓ1 := le_trans (Nat.succ_le_of_lt (by positivity)) hℓ
      hA := mul_clog_le (84 * (c + 1)) _ (by omega) hℓ
      hΔ2 := hΔ2
      hΔ := hΔ
      hnb := hnb
      hm := hm }
  exact ⟨b.hyp, b.r_le, b.beta_le, b.beta0_le_four, nb_mul_le n Δ, b.lt_two_mul⟩
end ClauseBound.ParityChecks
