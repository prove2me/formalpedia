-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_unit_atom_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:16:57.778214+00:00
-- url     : https://prove2.me/submissions/0642ac36-a327-490e-abff-aadb5037fea5

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The real Bochner integral of the unit-jump boundary correction
is exactly the scalar parameter times the real unit-atom mass. -/
theorem solution (μ : Measure ℝ) (θ : ℝ) :
    (∫ z in Ioi (0 : ℝ),
      θ * (if z = 1 then (1 : ℝ) else 0) ∂μ) =
        θ * μ.real ({1} : Set ℝ) := by
  have hpoint (z : ℝ) :
      θ * (if z = 1 then (1 : ℝ) else 0) =
      ({1} : Set ℝ).indicator (fun _ => θ) z := by
    by_cases hz : z = 1
    · subst z
      simp
    · simp [Set.indicator, hz]
  have hsub : ({1} : Set ℝ) ⊆ Ioi (0 : ℝ) := by
    intro z hz
    have heq : z = 1 := by simpa only [mem_singleton_iff] using hz
    subst z
    norm_num
  calc
    _ = ∫ z in Ioi (0 : ℝ),
      ({1} : Set ℝ).indicator (fun _ => θ) z ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ z in Ioi (0 : ℝ) ∩ ({1} : Set ℝ), θ ∂μ := by
      rw [setIntegral_indicator (measurableSet_singleton (1 : ℝ))]
    _ = ∫ z in ({1} : Set ℝ), θ ∂μ := by
      rw [inter_eq_right.mpr hsub]
    _ = μ.real ({1} : Set ℝ) * θ := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
    _ = _ := by ring
