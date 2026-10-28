-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_has_negative_left_shift_exponent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:32:06.952141+00:00
-- url     : https://prove2.me/submissions/8167cab7-6088-4198-af65-4104499bcdf5

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < φ ∧ X.ψ (φ - ε) < q := by
  refine ⟨φ / 2, by positivity, by linarith, ?_⟩
  have h := levy_psi_positive_secant_monotone X (φ / 2) φ (by positivity) (by linarith)
  rw [hroot, div_le_div_iff₀ (by positivity) hφ] at h
  have he : φ - φ / 2 = φ / 2 := by ring
  rw [he]
  nlinarith
