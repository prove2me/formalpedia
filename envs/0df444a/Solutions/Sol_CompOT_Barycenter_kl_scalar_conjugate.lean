-- Prove2me | solution 1 for CompOT.Barycenter.kl_scalar_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:01:15.948979+00:00
-- url     : https://prove2.me/submissions/fc1fb8c8-c8c0-43a2-86b7-09e18575b143

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs
set_option autoImplicit false

open CompOT.Barycenter in
theorem solution (u k : ℝ) (hk : 0 < k) :
    (∀ r : ℝ, 0 ≤ r → u * r - klEntry r k ≤ k * (Real.exp u - 1)) ∧
    0 ≤ k * Real.exp u ∧
    u * (k * Real.exp u) - klEntry (k * Real.exp u) k =
      k * (Real.exp u - 1) := by
  have hz : 0 < Real.exp u := Real.exp_pos u
  refine ⟨?_, (mul_pos hk hz).le, ?_⟩
  · intro r hr
    unfold klEntry
    by_cases h0 : r = 0
    · subst h0
      simp
      nlinarith [mul_pos hk hz]
    · have hr' : 0 < r := lt_of_le_of_ne hr (Ne.symm h0)
      simp only [h0, if_false]
      -- r * (u - log (r/k) + 1) ≤ k * exp u
      have hq : 0 < k * Real.exp u / r := by positivity
      have hlog := Real.log_le_sub_one_of_pos hq
      have hl : Real.log (k * Real.exp u / r) = Real.log k + u - Real.log r := by
        rw [Real.log_div (by positivity) h0, Real.log_mul hk.ne' hz.ne', Real.log_exp]
      have hl2 : Real.log (r / k) = Real.log r - Real.log k := Real.log_div h0 hk.ne'
      rw [hl] at hlog
      have : r * (Real.log k + u - Real.log r) ≤ r * (k * Real.exp u / r - 1) :=
        mul_le_mul_of_nonneg_left hlog hr
      have h3 : r * (k * Real.exp u / r - 1) = k * Real.exp u - r := by
        field_simp
      rw [hl2]
      nlinarith
  · unfold klEntry
    have hne : k * Real.exp u ≠ 0 := by positivity
    simp only [hne, if_false]
    rw [Real.log_div hne hk.ne', Real.log_mul hk.ne' hz.ne', Real.log_exp]
    ring
