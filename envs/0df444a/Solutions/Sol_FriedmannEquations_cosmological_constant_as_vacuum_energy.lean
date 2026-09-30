-- Prove2me | solution 1 for FriedmannEquations.cosmological_constant_as_vacuum_energy
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:35:16.533103+00:00
-- url     : https://prove2.me/submissions/320bee29-9b3e-4729-abbc-5f4f83a5e3df

import Definitions.Def_FriedmannEquations_Defs
set_option autoImplicit false
open FriedmannEquations

theorem solution (G Λ k : ℝ) (hG : 0 < G) (R ρ p : ℝ → ℝ) (t : ℝ) :
    (FirstFriedmannEq G Λ k R (fun s => ρ s - Λ / (8 * Real.pi * G)) t ↔
      FirstFriedmannEq G 0 k R ρ t) ∧
    (SecondFriedmannEq G Λ R (fun s => ρ s - Λ / (8 * Real.pi * G))
        (fun s => p s + Λ / (8 * Real.pi * G)) t ↔
      SecondFriedmannEq G 0 R ρ p t) := by
  unfold FirstFriedmannEq SecondFriedmannEq
  constructor <;> constructor <;> intro hh
  all_goals field_simp [hG.ne', Real.pi_ne_zero] at hh ⊢
  all_goals simp only [div_eq_mul_inv] at hh ⊢
  all_goals nlinarith

