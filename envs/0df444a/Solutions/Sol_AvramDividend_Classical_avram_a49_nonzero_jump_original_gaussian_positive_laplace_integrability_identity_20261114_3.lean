-- Prove2me | solution 3 for AvramDividend.Classical.avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:39:19.984204+00:00
-- url     : https://prove2.me/submissions/54567c56-47ab-4aba-bef1-3af4274c3beb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a64_source_gaussian_mgf_from_product_and_jump_exponents_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
    ∀ (t : ℝ≥0) (ht : 0 < t) (θ : ℝ), 0 < θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      mgf (G t) P θ =
        mgf id (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) θ := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t ht θ hθ
  obtain ⟨H, J, a, b, hMH, hMJ, hHEq, hJEq, hInd,
    hProd, hJInt, hSource, hJMean, hBalance⟩ :=
    avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
      X hX hFinite hPositive hNu R hR t ht θ hθ
  have hFM : Measurable (fun ω => Real.exp (θ * H ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hMH)
  have hJM : Measurable (fun ω => Real.exp (θ * J ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hMJ)
  have hProd' : Integrable
      (fun ω => Real.exp (θ * H ω) * Real.exp (θ * J ω)) P := by
    convert hProd using 1
    ext ω
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨hHInt, hFactor⟩ :=
    avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
      (fun ω => Real.exp (θ * H ω)) (fun ω => Real.exp (θ * J ω))
      hFM hJM hInd hProd'
      (avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114 J θ)
  have hFactor' :
      (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) =
        (∫ ω, Real.exp (θ * H ω) ∂P) *
          (∫ ω, Real.exp (θ * J ω) ∂P) := by
    convert hFactor using 1
    congr 1
    funext ω
    rw [mul_add, Real.exp_add]
  have hMeanH :=
    avram_a64_source_gaussian_mgf_from_product_and_jump_exponents_20261114
      H J θ a b ((t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2))
      hFactor' hSource hJMean hBalance
  have hGH : (fun ω => Real.exp (θ * G t ω)) =ᵐ[P]
      (fun ω => Real.exp (θ * H ω)) := by
    filter_upwards [hEq, hHEq] with ω hG hH
    simp [hG t, hH]
  have hGInt : Integrable (fun ω => Real.exp (θ * G t ω)) P :=
    hHInt.congr hGH.symm
  refine ⟨hGInt, ?_⟩
  have hMeanG : (∫ ω, Real.exp (θ * G t ω) ∂P) =
      Real.exp ((t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by
    calc
      _ = ∫ ω, Real.exp (θ * H ω) ∂P := integral_congr_ae hGH
      _ = _ := hMeanH
  change (∫ ω, Real.exp (θ * G t ω) ∂P) =
    mgf id (gaussianReal 0
      (NNReal.mk ((t : ℝ) * X.σ ^ 2)
        (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) θ
  rw [hMeanG, ProbabilityTheory.mgf_id_gaussianReal]
  all_goals simp
  all_goals ring
