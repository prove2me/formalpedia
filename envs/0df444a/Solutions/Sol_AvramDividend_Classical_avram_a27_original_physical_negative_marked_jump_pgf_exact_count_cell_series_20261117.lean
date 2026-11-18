-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:45:56.841376+00:00
-- url     : https://prove2.me/submissions/742b1d73-9e08-43b6-a396-aada964d2878

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The true original physical negative marked-jump joint generating function has its exact count-cell power-series coefficients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun k : ℕ => z ^ k *
      (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P))
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by
  have hInt :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK z hz hz1
  exact avram_a27_joint_marked_count_pgf_hasSum_exact_count_cell_coefficients_20261117
    P K hK (fun ω => Real.exp (θ * J ω)) z hInt
