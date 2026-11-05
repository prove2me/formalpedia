-- Prove2me | solution 1 for ClauseBound.Part.exists_le_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:36:41.533695+00:00
-- url     : https://prove2.me/submissions/c3809351-dae2-488a-ba23-be5abe528ed9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_cHR_pos
import Theorems.Thm_ClauseBound_Part_Lower_step
import Theorems.Thm_ClauseBound_Part_p_pos


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open Lower
namespace ClauseBound.Part
theorem _root_.solution : ∃ (H : ℝ) (B : ℕ), 0 < H ∧ ∀ E : ℕ, 1 ≤ E → H * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ B ≤ p E := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((4 * ((3890 : ℕ) : ℝ) / cHR + cHR) ^ 2)
  refine ⟨Real.exp (-(cHR * Real.sqrt n₀)), 3890, Real.exp_pos _, fun E => ?_⟩
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE
    rcases lt_or_ge E n₀ with h | h
    · have h1 : (1 : ℝ) ≤ p E := by exact_mod_cast p_pos E
      have h2 : (1 : ℝ) ≤ (E : ℝ) ^ 3890 := one_le_pow₀ (by exact_mod_cast hE)
      have h3 : Real.sqrt E ≤ Real.sqrt n₀ := Real.sqrt_le_sqrt (by exact_mod_cast h.le)
      have h4 : Real.exp (-(cHR * Real.sqrt n₀)) * Real.exp (cHR * Real.sqrt E) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff]
        have := mul_le_mul_of_nonneg_left h3 cHR_pos.le
        linarith
      refine le_trans ?_ h1
      rw [div_le_one (by positivity)]
      exact h4.trans h2
    · refine step (Real.exp_pos _).le (by norm_num) ?_ fun m hm1 hm => ih m hm hm1
      have h5 : ((4 * ((3890 : ℕ) : ℝ) / cHR + cHR) ^ 2) ≤ (E : ℝ) := hn₀.trans (by exact_mod_cast h)
      exact (le_abs_self _).trans (Real.abs_le_sqrt h5)
end ClauseBound.Part
