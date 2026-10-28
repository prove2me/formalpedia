-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_root_strictly_above_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:54:53.253968+00:00
-- url     : https://prove2.me/submissions/d3dd3850-c712-4455-a36a-6620d003be49

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
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
    q < X.ψ (φ + θ) := by
  have hsec := levy_psi_root_shifted_increment_lower
    X q φ θ hq hφ hθ hroot
  have hpos : 0 < (q / φ) * θ :=
    mul_pos (div_pos hq hφ) hθ
  linarith
