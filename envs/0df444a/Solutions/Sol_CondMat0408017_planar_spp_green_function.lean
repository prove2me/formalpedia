-- Prove2me | solution 1 for CondMat0408017.planar_spp_green_function
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:30:31.838858+00:00
-- url     : https://prove2.me/submissions/5e1f03a3-70e9-4473-b50e-68ce0f10ee76

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (eps a a0 : ℂ) (ha0 : a0 ≠ 0) :
    (eps * a0 + a ≠ 0 → ∀ G : ℂ,
      (2 * I * a0 * G + fresnelP eps a a0 = -1 ↔ G = I * eps / (eps * a0 + a))) ∧
    (a0 + a ≠ 0 → ∀ G : ℂ, (2 * I * a0 * G + fresnelS a a0 = -1 ↔ G = I / (a0 + a))) := by
  have h2Ia0 : 2 * I * a0 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) ha0
  constructor
  · intro hden G
    simp only [fresnelP]
    constructor
    · intro h
      have h1 : (2 * I * a0 * G + (eps * a0 - a) / (eps * a0 + a)) * (eps * a0 + a) =
          -1 * (eps * a0 + a) := congrArg (· * (eps * a0 + a)) h
      rw [add_mul, div_mul_cancel₀ _ hden] at h1
      rw [eq_div_iff hden]
      have h2 : 2 * I * a0 * (G * (eps * a0 + a) - I * eps) = 0 := by
        linear_combination h1 - 2 * a0 * eps * I_sq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2Ia0)
    · intro hG
      rw [hG]
      have h1 : (2 * I * a0 * (I * eps / (eps * a0 + a)) + (eps * a0 - a) / (eps * a0 + a)) *
          (eps * a0 + a) = -1 * (eps * a0 + a) := by
        rw [add_mul, mul_div_assoc', div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden]
        linear_combination 2 * a0 * eps * I_sq
      exact mul_right_cancel₀ hden h1
  · intro hden G
    simp only [fresnelS]
    constructor
    · intro h
      have h1 : (2 * I * a0 * G + (a0 - a) / (a0 + a)) * (a0 + a) =
          -1 * (a0 + a) := congrArg (· * (a0 + a)) h
      rw [add_mul, div_mul_cancel₀ _ hden] at h1
      rw [eq_div_iff hden]
      have h2 : 2 * I * a0 * (G * (a0 + a) - I) = 0 := by
        linear_combination h1 - 2 * a0 * I_sq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2Ia0)
    · intro hG
      rw [hG]
      have h1 : (2 * I * a0 * (I / (a0 + a)) + (a0 - a) / (a0 + a)) * (a0 + a) =
          -1 * (a0 + a) := by
        rw [add_mul, mul_div_assoc', div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden]
        linear_combination 2 * a0 * I_sq
      exact mul_right_cancel₀ hden h1
