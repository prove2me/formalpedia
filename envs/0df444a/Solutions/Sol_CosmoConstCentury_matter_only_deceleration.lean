-- Prove2me | solution 1 for CosmoConstCentury.matter_only_deceleration
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:05:12.591978+00:00
-- url     : https://prove2.me/submissions/fadd38f2-6acb-4a13-bfd3-e6faa63f064b

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

open CosmoConstCentury in
theorem solution (G c k : ℝ) (hG : 0 < G) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c 0 k I R ρ) (t : ℝ) (ht : t ∈ I) :
    deriv (deriv R) t / R t = -(4 * Real.pi * G / 3) * ρ t ∧
    (deriv R t ≠ 0 →
      decelParam R t = 4 * Real.pi * G / (3 * hubbleParam R t ^ 2) * ρ t ∧
      decelParam R t = omegaMatter G R ρ t / 2) := by
  obtain ⟨hr, -, h1, h2⟩ := hsol t ht
  have hκ : einsteinKappa G c * c ^ 2 = 8 * Real.pi * G := by
    unfold einsteinKappa
    field_simp
  rw [hκ] at h1
  have key : deriv (deriv R) t / R t = -(4 * Real.pi * G / 3) * ρ t := by
    linear_combination (3 * h2 - h1) / 6
  have hr0 : R t ≠ 0 := hr.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hG0 : G ≠ 0 := hG.ne'
  refine ⟨key, fun hD => ⟨?_, ?_⟩⟩
  · have hH : hubbleParam R t ≠ 0 := by
      unfold hubbleParam; exact div_ne_zero hD hr0
    unfold decelParam
    rw [key]
    field_simp
  · unfold decelParam omegaMatter criticalDensity hubbleParam
    rw [key]
    field_simp
    ring
