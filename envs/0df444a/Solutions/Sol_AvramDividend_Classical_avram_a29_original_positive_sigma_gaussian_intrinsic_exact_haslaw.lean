-- Prove2me | solution 1 for AvramDividend.Classical.avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:53:11.475547+00:00
-- url     : https://prove2.me/submissions/dfe0bc8c-8dd9-490a-9078-4c2eb30428ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_positive_sigma_gaussian_source_charfun_real_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical Gaussian marginal law follows from source measurability, exact original Fourier law and uniqueness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ t : ℝ≥0,
      HasLaw (G t)
        (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMeas :=
    avram_a31_original_gaussian_source_ae_representative_measurable_20261114
      X R hR G hEq
  have hChar :=
    avram_a31_original_positive_sigma_gaussian_source_charfun_real_20261114
      X hX hFinite hPositive R hR G hEq
  intro t
  exact avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
    (G t)
    (NNReal.mk ((t : ℝ) * X.σ ^ 2)
      (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))
    (hMeas t) (hChar t)
