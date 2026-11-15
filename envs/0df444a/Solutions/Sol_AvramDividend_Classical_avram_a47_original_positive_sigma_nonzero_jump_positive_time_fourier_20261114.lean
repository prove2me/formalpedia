-- Prove2me | solution 1 for AvramDividend.Classical.avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:41:52.687958+00:00
-- url     : https://prove2.me/submissions/671b53e8-8ccc-4652-a1c4-c8b7c4ca2fe0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (ht : 0 < t) (u : ℝ),
      charFun (P.map (G t)) u =
        charFun (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) u := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMeas :=
    avram_a31_original_gaussian_source_ae_representative_measurable_20261114
      X R hR G hEq
  intro t ht u
  have hSource :=
    avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
      X hX hFinite hPositive hNu R hR G hEq t ht
  have hInt (θ : ℝ) (hθ : 0 < θ) :
      Integrable (fun ω => Real.exp (θ * G t ω)) P :=
    (hSource θ hθ).1
  have hMGF (θ : ℝ) (hθ : 0 < θ) :
      mgf (G t) P θ =
        mgf id (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) θ :=
    (hSource θ hθ).2
  have hLaw :=
    avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
      P (G t) (hMeas t)
      (NNReal.mk ((t : ℝ) * X.σ ^ 2)
        (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))
      hInt hMGF
  exact congrArg (fun μ : Measure ℝ => charFun μ u) hLaw.map_eq
