-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_root_shifted_increment_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:58:32.760854+00:00
-- url     : https://prove2.me/submissions/eb662957-599d-4bd9-aed8-3378734f1e21

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
    (q φ θ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hroot : X.ψ φ = q) :
    (q / φ) * θ ≤ X.ψ (φ + θ) - q := by
  have hsum : 0 < φ + θ := by linarith
  have hsec : q / φ ≤ X.ψ (φ + θ) / (φ + θ) := by
    simpa only [hroot] using
      levy_psi_positive_secant_monotone X φ (φ + θ) hφ (by linarith)
  have hmul : q * (φ + θ) ≤ X.ψ (φ + θ) * φ :=
    (div_le_div_iff₀ hφ hsum).mp hsec
  have hfactor : (q / φ) * φ = q := by
    field_simp
  have hm : ((q / φ) * θ) * φ ≤ (X.ψ (φ + θ) - q) * φ := by
    calc
      ((q / φ) * θ) * φ = q * θ := by
        calc
          _ = ((q / φ) * φ) * θ := by ring
          _ = q * θ := by rw [hfactor]
      _ ≤ (X.ψ (φ + θ) - q) * φ := by nlinarith [hmul]
  by_contra hc
  exact (not_lt_of_ge hm)
    (mul_lt_mul_of_pos_right (lt_of_not_ge hc) hφ)
