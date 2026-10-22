-- Prove2me | solution 1 for BootRobust.NWDual.fenchel_xlogx
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:08:16.796716+00:00
-- url     : https://prove2.me/submissions/ffc16aba-4135-41f4-b2d8-110d7144921d

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

set_option autoImplicit false

theorem solution (ν b : ℝ) (hν : 0 < ν) :
    IsGreatest {x : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ x = lam * b - ν * lam * Real.log lam}
      (ν * Real.exp (b / ν - 1)) := by
  constructor
  · refine ⟨Real.exp (b / ν - 1), (Real.exp_pos _).le, ?_⟩
    rw [Real.log_exp]
    field_simp
    ring
  · rintro x ⟨lam, hlam, rfl⟩
    rcases hlam.eq_or_lt with h0 | hpos
    · subst h0
      simp
      positivity
    · set E := Real.exp (b / ν - 1) with hE
      have hEpos : 0 < E := Real.exp_pos _
      set u := lam / E with hu
      have hupos : 0 < u := div_pos hpos hEpos
      have hlog : Real.log lam = Real.log u + (b / ν - 1) := by
        have : lam = u * E := by rw [hu]; field_simp
        conv_lhs => rw [this]
        rw [Real.log_mul hupos.ne' hEpos.ne', hE, Real.log_exp]
      have hk := Real.one_sub_inv_le_log_of_pos hupos
      have e1 : lam * b - ν * lam * Real.log lam = ν * lam * (1 - Real.log u) := by
        rw [hlog]; field_simp; ring
      have e2 : ν * lam * u⁻¹ = ν * E := by
        rw [hu]; field_simp
      rw [e1, ← e2]
      have : 1 - Real.log u ≤ u⁻¹ := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
