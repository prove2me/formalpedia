-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_canonical_finite_esscher_increment_vector_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:23:38.21652+00:00
-- url     : https://prove2.me/submissions/d550a82a-27dd-4af2-b94a-b0b39656ca4f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_canonical_esscher_density_eq_displacement_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_finite_terminal_esscher_increment_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Full increment-vector reversal for the *canonical* Q_T Esscher law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ) :
    Measure.map (fun v : Fin n → ℝ => fun i => v i.rev)
      (Measure.map
        (fun ω : Ω => fun i : Fin n =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((i.val : ℝ≥0) * δ) ω)
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X ((n : ℝ≥0) * δ) ω -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))) =
    Measure.map
      (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X ((n : ℝ≥0) * δ) ω -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) := by
  have h :=
    avram_ws01e_b_true_finite_terminal_esscher_increment_reversal
      X δ n θ
  have hEq :=
    avram_ws01e_b_canonical_esscher_density_eq_displacement_density
      X θ ((n : ℝ≥0) * δ)
  rw [hEq] at h
  exact h
