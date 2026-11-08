-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_compensated_exp_moment_of_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:41:38.915194+00:00
-- url     : https://prove2.me/submissions/50a76aad-666e-4d13-8012-c690fb26c73b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite-band Poisson count has the compensated exponential
moment, explicitly conditional on its full original probability law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (NB : Ω → ℕ)
    (hcount : ∀ ω, (NB ω : ℝ≥0∞) =
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Set.Ioc (0 : ℝ≥0) T ×ˢ B))
    (hNm : Measurable NB)
    (r : ℝ≥0)
    (hLaw : P.map NB = poissonMeasure r)
    (θ : ℝ) :
    (∫ ω, Real.exp (θ * ((NB ω : ℝ) - (r : ℝ))) ∂P) =
      Real.exp ((r : ℝ) * (Real.exp θ - 1 - θ)) := by
  have hpoint (ω : Ω) :
      Real.exp (θ * ((NB ω : ℝ) - (r : ℝ))) =
        Real.exp (-(θ * (r : ℝ))) * (Real.exp θ) ^ NB ω := by
    have heq : θ * ((NB ω : ℝ) - (r : ℝ)) =
        -(θ * (r : ℝ)) + (NB ω : ℝ) * θ := by ring
    rw [heq, Real.exp_add, Real.exp_nat_mul]
  calc
    (∫ ω, Real.exp (θ * ((NB ω : ℝ) - (r : ℝ))) ∂P) =
        ∫ ω, Real.exp (-(θ * (r : ℝ))) *
          (Real.exp θ) ^ NB ω ∂P := by simp_rw [hpoint]
    _ = Real.exp (-(θ * (r : ℝ))) *
        (∫ ω, (Real.exp θ) ^ NB ω ∂P) := by rw [integral_const_mul]
    _ = Real.exp ((r : ℝ) * (Real.exp θ - 1 - θ)) := by
      rw [avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law
        X T B NB hcount hNm r hLaw (Real.exp θ)]
      rw [← Real.exp_add]
      congr 1
      ring
