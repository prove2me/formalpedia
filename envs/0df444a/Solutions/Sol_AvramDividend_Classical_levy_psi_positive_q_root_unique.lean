-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_positive_q_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:33:52.756004+00:00
-- url     : https://prove2.me/submissions/8be780a5-a21d-4b74-bb4f-c219181c241b

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ η : ℝ) (hq : 0 < q)
    (hφ : 0 < φ) (hη : 0 < η)
    (hrootφ : X.ψ φ = q) (hrootη : X.ψ η = q) :
    φ = η := by
  rcases le_total φ η with hle | hle
  · have hsec : X.ψ φ / φ ≤ X.ψ η / η :=
      levy_psi_positive_secant_monotone X φ η hφ hle
    rw [hrootφ, hrootη] at hsec
    have hmul : q * η ≤ q * φ :=
      (div_le_div_iff₀ hφ hη).mp hsec
    have hback : η ≤ φ := by nlinarith
    exact le_antisymm hle hback
  · have hsec : X.ψ η / η ≤ X.ψ φ / φ :=
      levy_psi_positive_secant_monotone X η φ hη hle
    rw [hrootη, hrootφ] at hsec
    have hmul : q * φ ≤ q * η :=
      (div_le_div_iff₀ hη hφ).mp hsec
    have hback : φ ≤ η := by nlinarith
    exact le_antisymm hback hle
