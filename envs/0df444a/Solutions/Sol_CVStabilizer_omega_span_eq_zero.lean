-- Prove2me | solution 1 for CVStabilizer.omega_span_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:18:25.81494+00:00
-- url     : https://prove2.me/submissions/2e0beacc-cd57-4f09-bc63-c76c2edf39d9

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

open CVStabilizer in
theorem solution (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    ∀ v ∈ Submodule.span ℝ (Set.range u), ∀ v' ∈ Submodule.span ℝ (Set.range u),
      omega n v v' = 0 := by
  have step1 : ∀ i, ∀ v' ∈ Submodule.span ℝ (Set.range u), omega n (u i) v' = 0 := by
    intro i v' hv'
    have hle : Submodule.span ℝ (Set.range u) ≤ LinearMap.ker (omega n (u i)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact hiso i j
    exact LinearMap.mem_ker.mp (hle hv')
  intro v hv v' hv'
  have hle : Submodule.span ℝ (Set.range u) ≤ LinearMap.ker (LinearMap.flip (omega n) v') := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact step1 i v' hv'
  have := LinearMap.mem_ker.mp (hle hv)
  rwa [LinearMap.flip_apply] at this
