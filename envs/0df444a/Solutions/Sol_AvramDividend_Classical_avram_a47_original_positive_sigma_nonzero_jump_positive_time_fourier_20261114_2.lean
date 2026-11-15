-- Prove2me | solution 2 for AvramDividend.Classical.avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:15:31.912951+00:00
-- url     : https://prove2.me/submissions/51ccd3c7-433d-44a6-a61a-9f4984799273
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
  intro t ht u
  have hMeas : AEMeasurable (G t) P :=
    avram_a31_original_gaussian_source_ae_representative_measurable_20261114
      X R hR G hEq t
  have hLap := fun θ (hθ : 0 < θ) =>
    avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
      X hX hFinite hPositive hNu R hR G hEq t ht θ hθ
  have hLaw : HasLaw (G t)
      (gaussianReal 0
        (NNReal.mk ((t : ℝ) * X.σ ^ 2)
          (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) P :=
    avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
      P (G t) hMeas _ (fun θ hθ => (hLap θ hθ).1)
      (fun θ hθ => (hLap θ hθ).2)
  exact congrArg (fun μ : Measure ℝ => charFun μ u) hLaw.map_eq
