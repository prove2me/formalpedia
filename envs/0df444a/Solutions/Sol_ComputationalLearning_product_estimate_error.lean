-- Prove2me | solution 1 for ComputationalLearning.product_estimate_error
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:16:05.568166+00:00
-- url     : https://prove2.me/submissions/42fa5023-50b4-42df-b91b-2c1438328e63

import Mathlib
import Definitions.Def_ComputationalLearning_Noise

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open ComputationalLearning in
theorem solution {A B Ah Bh τ' : ℝ} (hA : A ∈ Set.Icc (0 : ℝ) 1)
    (hB : B ∈ Set.Icc (0 : ℝ) 1) (hAh : Ah ∈ Set.Icc (0 : ℝ) 1) (hBh : Bh ∈ Set.Icc (0 : ℝ) 1)
    (hτ : τ' ∈ Set.Icc (0 : ℝ) 1) (h1 : |A - Ah| ≤ τ') (h2 : |B - Bh| ≤ τ') :
    A * B - 2 * τ' ≤ Ah * Bh ∧ Ah * Bh ≤ A * B + 3 * τ' := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  obtain ⟨hAh0, hAh1⟩ := hAh
  obtain ⟨hBh0, hBh1⟩ := hBh
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  -- Ah*Bh - A*B = Ah*(Bh - B) + B*(Ah - A)
  have e : Ah * Bh - A * B = Ah * (Bh - B) + B * (Ah - A) := by ring
  have k1 : Ah * (Bh - B) ≤ τ' := by nlinarith
  have k2 : -τ' ≤ Ah * (Bh - B) := by nlinarith
  have k3 : B * (Ah - A) ≤ τ' := by nlinarith
  have k4 : -τ' ≤ B * (Ah - A) := by nlinarith
  constructor <;> nlinarith

