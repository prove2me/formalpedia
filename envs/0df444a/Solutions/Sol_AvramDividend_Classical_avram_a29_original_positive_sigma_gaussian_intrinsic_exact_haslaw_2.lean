-- Prove2me | solution 2 for AvramDividend.Classical.avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:48:23.868233+00:00
-- url     : https://prove2.me/submissions/ba316259-6d1b-48f8-84a7-e951b92bce54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
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
  intro t
  by_cases ht0 : t = 0
  · subst t
    have hChar :=
      avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
        X R hR G hEq
    have hLaw0 :=
      avram_a31_charfun_identifies_gaussian_haslaw_real_20261114
        (G 0) 0 (hMeas 0) hChar
    simpa using hLaw0
  · have ht : 0 < t := lt_of_le_of_ne (by positivity : 0 ≤ t) (Ne.symm ht0)
    by_cases hNu : X.ν = 0
    · have hPhysical :=
        avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
          X hNu hPositive R hR t
      have hMap : Measure.map (G t) P = Measure.map (R t) P := by
        apply Measure.map_congr
        filter_upwards [hEq] with ω hω
        exact hω t
      have hv :
          (NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t =
            NNReal.mk ((t : ℝ) * X.σ ^ 2)
              (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)) := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_mul, NNReal.coe_mk]
        ring
      refine ⟨hMeas t, ?_⟩
      calc
        Measure.map (G t) P = Measure.map (R t) P := hMap
        _ = gaussianReal 0 ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) :=
          hPhysical
        _ = gaussianReal 0 (NNReal.mk ((t : ℝ) * X.σ ^ 2)
          (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))) := by rw [hv]
    · have hSource :=
        avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
          X hX hFinite hPositive hNu R hR G hEq t ht
      have hInt (θ : ℝ) (hθ : 0 < θ) :
          Integrable (fun ω => Real.exp (θ * G t ω)) P := (hSource θ hθ).1
      have hMGF (θ : ℝ) (hθ : 0 < θ) :
          mgf (G t) P θ =
            mgf id (gaussianReal 0
              (NNReal.mk ((t : ℝ) * X.σ ^ 2)
                (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) θ :=
        (hSource θ hθ).2
      exact
        avram_a48_original_ae_positive_mgf_identifies_gaussian_haslaw_20261114
          P (G t) (hMeas t)
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))
          hInt hMGF
