-- Prove2me | solution 1 for BitDFT.disc_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:58:14.188645+00:00
-- url     : https://prove2.me/submissions/382d8097-04d6-47b9-98b4-71234d8268b8

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic
open BitDFT

private theorem coordinate_bounds (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) :
    z.1.natAbs ≤ 2^p ∧ z.2.natAbs ≤ 2^p := by
  have hp : (0 : ℝ) < 2^p := by positivity
  have hn : ‖(z.1 : ℂ) + (z.2 : ℂ) * Complex.I‖ ≤ (2 : ℝ)^p := by
    unfold inDisc value at h
    rw [norm_div, norm_pow] at h
    norm_num at h
    exact (div_le_iff₀ hp).mp h |>.trans (by simp)
  have hre := (Complex.abs_re_le_norm ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).trans hn
  have him := (Complex.abs_im_le_norm ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).trans hn
  simp at hre him
  constructor
  · have hc : (z.1.natAbs : ℝ) ≤ (2 : ℝ)^p := by simpa [Nat.cast_natAbs] using hre
    exact_mod_cast hc
  · have hc : (z.2.natAbs : ℝ) ≤ (2 : ℝ)^p := by simpa [Nat.cast_natAbs] using him
    exact_mod_cast hc

theorem solution (p : ℕ) (z : ℤ × ℤ) (h : inDisc p z) :
    (z.1.natAbs < 2^p ∨ z.1.natAbs = 2^p) ∧
    (z.2.natAbs < 2^p ∨ z.2.natAbs = 2^p) := by
  obtain ⟨hr,hi⟩ := coordinate_bounds p z h
  exact ⟨lt_or_eq_of_le hr,lt_or_eq_of_le hi⟩
