-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27_original_finite_horizon_discounted_real_integral_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T11:27:37.611486+00:00
-- url     : https://prove2.me/submissions/5dd6a7f6-2953-4aa9-bc8c-5320ba423de7

import Mathlib

open Classical MeasureTheory Set Filter intervalIntegral
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution (q T : ℝ) :
    q * (∫ t in (0 : ℝ)..T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ)) +
      Real.exp (-(q * T)) = 1 := by
  by_cases hq : q = 0
  · subst hq
    simp
  · let F : ℝ → ℝ := fun y => -(1 / q) * Real.exp (-(q * y))
    have hexp : ∀ x, HasDerivAt (fun y : ℝ => Real.exp (-(q * y)))
        ((-q) * Real.exp (-(q * x))) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => (-q) * y) (-q) x := by
        simpa using (hasDerivAt_id (𝕜 := ℝ) x).const_mul (-q)
      have hfun : (fun y : ℝ => Real.exp (-(q * y))) = fun y => Real.exp ((-q) * y) := by
        funext y; ring_nf
      rw [hfun, show -(q * x) = (-q) * x by ring]
      simpa [mul_comm] using hlin.exp
    have hderiv : ∀ x, HasDerivAt F (Real.exp (-(q * x))) x := by
      intro x
      have h : HasDerivAt (fun y => -(1 / q) * Real.exp (-(q * y)))
          (-(1 / q) * ((-q) * Real.exp (-(q * x)))) x :=
        (hexp x).const_mul (-(1 / q))
      exact (h.congr_deriv (by field_simp [hq]))
    have hcont : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by continuity
    have hint : IntervalIntegrable (fun t => Real.exp (-(q * t))) volume 0 T :=
      hcont.intervalIntegrable 0 T
    have hftc :=
      integral_eq_sub_of_hasDerivAt (f := F) (f' := fun t => Real.exp (-(q * t)))
        (fun x _ => hderiv x) hint
    have hdiff : F T - F 0 = (1 - Real.exp (-(q * T))) / q := by
      change -(1 / q) * Real.exp (-(q * T)) - (-(1 / q) * Real.exp (-(q * (0 : ℝ)))) =
        (1 - Real.exp (-(q * T))) / q
      simp
      field_simp [hq]
      ring
    calc
      q * (∫ t in (0 : ℝ)..T, Real.exp (-(q * t))) + Real.exp (-(q * T))
          = q * (F T - F 0) + Real.exp (-(q * T)) := by rw [hftc]
      _ = q * ((1 - Real.exp (-(q * T))) / q) + Real.exp (-(q * T)) := by rw [hdiff]
      _ = 1 := by field_simp [hq]; ring
