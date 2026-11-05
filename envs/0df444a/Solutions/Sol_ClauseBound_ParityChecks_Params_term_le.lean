-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.term_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:14.011239+00:00
-- url     : https://prove2.me/submissions/b262a118-f60b-4d60-bd6b-7ac50cf35781

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_Rec_sum_choose_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
namespace ClauseBound.ParityChecks.Params
theorem _root_.solution {u i nb i₀ m h : ℕ} (hu : u ≤ m) (hi : i₀ ≤ i) (hi0 : 1 ≤ i₀) (hnb : 1 ≤ nb) (key : 6 * m * 2 ^ h ≤ nb * i₀) :
    |(-2 * (1 / (nb : ℝ))) ^ i * (u.choose i : ℝ)| ≤ (1 / 2 ^ h) ^ i := by
  by_cases hiu : u < i
  · rw [Nat.choose_eq_zero_of_lt hiu]
    simp only [Nat.cast_zero, mul_zero, abs_zero]
    positivity
  have hi1 : 1 ≤ i := hi0.trans hi
  have hnb' : (0 : ℝ) < nb := by exact_mod_cast hnb
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi1
  have h1 : (u.choose i : ℝ) ≤ (3 * u / i) ^ i :=
    le_trans (single_le_sum (f := fun ν => (u.choose ν : ℝ)) (fun _ _ => by positivity) (mem_range.2 (by omega)))
      (ClauseBound.Rec.sum_choose_le hi1 (by omega))
  have h2 : |(-2 * (1 / (nb : ℝ))) ^ i| = (2 / nb) ^ i := by
    rw [abs_pow]
    congr 1
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity)]
    ring
  have h3 : 2 / (nb : ℝ) * (3 * u / i) ≤ 1 / 2 ^ h := by
    have h4 : 6 * u * 2 ^ h ≤ nb * i :=
      le_trans (by gcongr) (le_trans key (Nat.mul_le_mul_left _ hi))
    have h5 : (6 : ℝ) * u * 2 ^ h ≤ nb * i := by exact_mod_cast h4
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  rw [abs_mul, h2, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u.choose i : ℝ))]
  calc (2 / (nb : ℝ)) ^ i * (u.choose i : ℝ) ≤ (2 / nb) ^ i * (3 * u / i) ^ i := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 / nb * (3 * u / i)) ^ i := by rw [mul_pow]
    _ ≤ (1 / 2 ^ h) ^ i := pow_le_pow_left₀ (by positivity) h3 i
end ClauseBound.ParityChecks.Params
