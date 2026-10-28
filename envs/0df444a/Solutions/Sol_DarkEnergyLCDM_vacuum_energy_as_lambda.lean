-- Prove2me | solution 1 for DarkEnergyLCDM.vacuum_energy_as_lambda
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:31.913314+00:00
-- url     : https://prove2.me/submissions/bac3faca-6058-49fb-9423-c9cb62e67f7d

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Real
open DarkEnergyLCDM

theorem solution (G K Λ : ℝ) (hG : G ≠ 0) (a ρ p : ℝ → ℝ) (t : ℝ) :
    (FriedmannEq G K Λ a ρ t ↔
      FriedmannEq G K 0 a (fun s => ρ s + Λ / (8 * π * G)) t) ∧
    (AccelerationEq G Λ a ρ p t ↔
      AccelerationEq G 0 a (fun s => ρ s + Λ / (8 * π * G))
        (fun s => p s - Λ / (8 * π * G)) t) ∧
    ContinuityEq a (fun _ => Λ / (8 * π * G)) (fun _ => -(Λ / (8 * π * G))) t := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have e1 : 8 * π * G / 3 * (ρ t + Λ / (8 * π * G)) = 8 * π * G / 3 * ρ t + Λ / 3 := by
    field_simp
  have e2 : -(4 * π * G / 3) * (ρ t + Λ / (8 * π * G) + 3 * (p t - Λ / (8 * π * G)))
      = -(4 * π * G / 3) * (ρ t + 3 * p t) + Λ / 3 := by
    field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold FriedmannEq; simp only [e1]; constructor <;> intro h <;> linarith
  · unfold AccelerationEq; simp only [e2]; constructor <;> intro h <;> linarith
  · unfold ContinuityEq; simp
