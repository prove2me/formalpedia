-- Prove2me | solution 1 for Eight.eStar_le_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:28:41.053283+00:00
-- url     : https://prove2.me/submissions/e284fea1-04ec-438a-af5b-f0e95ddcda57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_Eight_SecLevel_EStar
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Paper_achievable_of_eStar_lt
import Theorems.Thm_Paper_eStar_le
import Theorems.Thm_Paper_eStar_nonneg


set_option autoImplicit false
section
section
open Eight
open Paper
namespace Eight
theorem _root_.solution (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K))
    {e e'' : ℝ} (he : eStar < e) (he'' : rho * e < e'') : eStar ≤ e'' := by
  have hs0 := eStar_nonneg
  have h0 : 0 ≤ e := by linarith
  have hd : 0 < e'' - rho * e := by linarith
  have hρe : 0 ≤ rho * e := mul_nonneg (by unfold rho; norm_num) h0
  refine eStar_le (by linarith) fun K₀ => ?_
  obtain ⟨K, hK, hA⟩ := achievable_of_eStar_lt he (max K₀ (max 2 ⌈(2 * e + 2) / (e'' - rho * e)⌉₊))
  have hK0 : K₀ ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
  have hKd : (2 * e + 2) / (e'' - rho * e) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hK)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hsmall : (2 * e + 2) / (K : ℝ) ≤ e'' - rho * e := by
    rw [div_le_iff₀ hd] at hKd
    rw [div_le_iff₀ hKpos]
    linarith
  have hexp : (rho + 2 / K) * e + 2 / K ≤ e'' := by
    have : (rho + 2 / K) * e + 2 / K = rho * e + (2 * e + 2) / (K : ℝ) := by ring
    linarith
  refine ⟨9 * K ^ 16, ?_, (hP3 hK2 h0 hA).mono hexp⟩
  have : K ≤ K ^ 16 := Nat.le_self_pow (by norm_num) K
  omega
end Eight
