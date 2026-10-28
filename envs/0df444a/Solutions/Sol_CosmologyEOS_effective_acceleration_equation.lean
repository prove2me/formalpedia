-- Prove2me | solution 1 for CosmologyEOS.effective_acceleration_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:10:42.373675+00:00
-- url     : https://prove2.me/submissions/93b05129-467d-4ab8-aa5f-1f3e66a47390

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

theorem solution (G Λ : ℝ) (hG : G ≠ 0) (a ε p : ℝ → ℝ) (t : ℝ) :
    (AccelerationEquation G Λ a ε p t ↔
      deriv (deriv a) t / a t =
        -(4 / 3) * π * G *
          (effectiveEnergyDensity G Λ (ε t) + 3 * effectivePressure G Λ (p t))) ∧
    (effectiveEnergyDensity G Λ (ε t) ≠ 0 →
      -(4 / 3) * π * G *
          (effectiveEnergyDensity G Λ (ε t) + 3 * effectivePressure G Λ (p t)) =
        -(4 / 3) * π * G *
          (1 + 3 * eosParameter (effectivePressure G Λ (p t)) (effectiveEnergyDensity G Λ (ε t))) *
          effectiveEnergyDensity G Λ (ε t)) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have e : -(4 / 3) * π * G *
          (effectiveEnergyDensity G Λ (ε t) + 3 * effectivePressure G Λ (p t))
        = (Λ - 4 * π * G * (ε t + 3 * p t)) / 3 := by
    unfold effectiveEnergyDensity effectivePressure
    field_simp; ring
  refine ⟨?_, fun h => ?_⟩
  · rw [e]; unfold AccelerationEquation
    constructor <;> intro h <;> linarith
  · unfold eosParameter
    field_simp
