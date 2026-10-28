-- Prove2me | solution 2 for AvramDividend.Classical.esscher_positive_root_has_negative_left_shift_exponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:32:27.591212+00:00
-- url     : https://prove2.me/submissions/77d736fa-4101-4d1c-b880-e1bdaf1b02bc

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < φ ∧ X.ψ (φ - ε) < q := by
  refine ⟨φ / 2, by linarith, by linarith, ?_⟩
  have hhalfpos : 0 < φ / 2 := by linarith
  have hhalf : φ / 2 ≤ φ := by linarith
  have hsec := levy_psi_positive_secant_monotone X
    (φ / 2) φ hhalfpos hhalf
  have hprod : X.ψ (φ / 2) ≤ (X.ψ φ / φ) * (φ / 2) :=
    (div_le_iff₀ hhalfpos).mp hsec
  have hmul : (q / φ) * (φ / 2) = q / 2 := by
    field_simp
  have hbound : X.ψ (φ / 2) ≤ q / 2 := by
    calc
      X.ψ (φ / 2) ≤ (X.ψ φ / φ) * (φ / 2) := hprod
      _ = q / 2 := by rw [hroot]; exact hmul
  have hshift : φ - φ / 2 = φ / 2 := by ring
  rw [hshift]
  linarith
