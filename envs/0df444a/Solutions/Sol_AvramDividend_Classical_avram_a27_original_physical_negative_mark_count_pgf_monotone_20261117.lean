-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_mark_count_pgf_monotone_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:33:19.990874+00:00
-- url     : https://prove2.me/submissions/5d20b694-c236-45da-912a-9a5e3e372ab3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_bounded_marked_count_pgf_monotone_unit_interval_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original actual negative physical jump marked-count PGF is monotone. -/
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
    (z w : ℝ) (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w ≤ 1) :
    (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ≤
      (∫ ω, w ^ K ω * Real.exp (θ * J ω) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBound :=
    avram_a27_original_physical_negative_jump_laplace_factor_le_one_20261117
      X hFinite t θ hθ J hJEq
  have hMeas : Measurable (fun ω => Real.exp (θ * J ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hJMeas)
  exact avram_a27_bounded_marked_count_pgf_monotone_unit_interval_20261117
    P K hK (fun ω => Real.exp (θ * J ω)) hMeas
    (hBound.mono fun ω h => ⟨le_of_lt h.1, h.2⟩)
    z w hz hzw hw
