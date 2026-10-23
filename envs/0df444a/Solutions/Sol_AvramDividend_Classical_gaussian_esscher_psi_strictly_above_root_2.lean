-- Prove2me | solution 2 for AvramDividend.Classical.gaussian_esscher_psi_strictly_above_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:45:47.268328+00:00
-- url     : https://prove2.me/submissions/0fd76f07-ed7c-47db-92e4-895e6a4ec2cb

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive secants force strict crossing above every positive q-root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hθ : 0 < θ) (hσ : 0 < X.σ) (hroot : X.ψ φ = q)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(X.ν.map (fun y : ℝ => -y))) < ⊤) :
    q < X.ψ (φ + θ) := by
  have hφθ : 0 < φ + θ := by linarith
  have hφle : φ ≤ φ + θ := by linarith
  have hsec : X.ψ φ / φ ≤ X.ψ (φ + θ) / (φ + θ) :=
    levy_psi_positive_secant_monotone X φ (φ + θ) hφ hφle
  rw [hroot] at hsec
  have hcross : q * (φ + θ) ≤ X.ψ (φ + θ) * φ :=
    (div_le_div_iff₀ hφ hφθ).mp hsec
  by_contra hbad
  have hle : X.ψ (φ + θ) ≤ q := le_of_not_gt hbad
  have hmul := mul_le_mul_of_nonneg_right hle hφ.le
  have hqθ : 0 < q * θ := mul_pos hq hθ
  nlinarith
