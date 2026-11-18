-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:19:22.313014+00:00
-- url     : https://prove2.me/submissions/3f908b13-d8b5-4860-98fe-c0d78b8a8487

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_bounded_marked_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original physical negative-mark Poisson joint PGF is an integrable observable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Integrable (fun ω => z ^ (K ω) * Real.exp (θ * J ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBounds :=
    avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
      X hFinite t θ hθ J hJEq
  have hMeas : Measurable (fun ω => Real.exp (θ * J ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hJMeas)
  exact avram_a27_bounded_marked_count_pgf_integrable_20261117
    P K hK (fun ω => Real.exp (θ * J ω))
    hMeas (hBounds.mono fun ω h => ⟨le_of_lt h.1, h.2⟩)
    z hz hz1
