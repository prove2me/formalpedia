-- Prove2me | solution 1 for CosmoConstCentury.deceleration_parameter_and_cosmic_acceleration
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:33:30.167286+00:00
-- url     : https://prove2.me/submissions/888ffce9-7472-4618-bbdc-e88b944e33d3

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

open CosmoConstCentury in
theorem solution (G c Λ k : ℝ) (hG : 0 < G) (hc : 0 < c)
    (I : Set ℝ) (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ k I R ρ) (t : ℝ) (ht : t ∈ I) :
    (deriv R t ≠ 0 → decelParam R t = omegaMatter G R ρ t / 2 - omegaLambda Λ R t) ∧
    (0 < deriv (deriv R) t → 0 ≤ ρ t → 0 < Λ) := by
  obtain ⟨hr, -, h1, h2⟩ := hsol t ht
  have hκ : einsteinKappa G c * c ^ 2 = 8 * Real.pi * G := by
    unfold einsteinKappa
    field_simp
  rw [hκ] at h1
  have key : deriv (deriv R) t / R t = (Λ - 4 * Real.pi * G * ρ t) / 3 := by
    linear_combination (3 * h2 - h1) / 6
  have hr0 : R t ≠ 0 := hr.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hG0 : G ≠ 0 := hG.ne'
  refine ⟨fun hD => ?_, fun hA hρ => ?_⟩
  · unfold decelParam omegaMatter omegaLambda criticalDensity hubbleParam
    rw [key]
    field_simp
    ring
  · have h3 : 0 < deriv (deriv R) t / R t := div_pos hA hr
    rw [key] at h3
    have : 0 ≤ 4 * Real.pi * G * ρ t := by
      have := Real.pi_pos
      positivity
    linarith
