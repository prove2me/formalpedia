-- Prove2me | solution 2 for AvramDividend.Classical.avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:39:05.02573+00:00
-- url     : https://prove2.me/submissions/40e79dcc-5233-4b10-90f8-b6865b15c96e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a64_source_gaussian_mgf_from_product_and_jump_exponents_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
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
  obtain ⟨H, J, a, b, hHm, hJm, hHEq, hJEq, hInd, hProd,
      hJInt, hSource, hJump, hBalance⟩ :=
    avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
      X hX hFinite hPositive hNu R hR t ht θ hθ
  have hFMeas : Measurable (fun ω => Real.exp (θ * H ω)) := by fun_prop
  have hJMeas : Measurable (fun ω => Real.exp (θ * J ω)) := by fun_prop
  have hProdInt :
      Integrable (fun ω => Real.exp (θ * H ω) * Real.exp (θ * J ω)) P := by
    simpa only [mul_add, Real.exp_add] using hProd
  obtain ⟨hHInt, hFactor⟩ :=
    avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
      (fun ω => Real.exp (θ * H ω))
      (fun ω => Real.exp (θ * J ω))
      hFMeas hJMeas hInd hProdInt
      (avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114 J θ)
  have hFactorExp :
      (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) =
        (∫ ω, Real.exp (θ * H ω) ∂P) *
          (∫ ω, Real.exp (θ * J ω) ∂P) := by
    simpa only [mul_add, Real.exp_add] using hFactor
  have hHExp :=
    avram_a64_source_gaussian_mgf_from_product_and_jump_exponents_20261114
      H J θ a b ((t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2))
      hFactorExp hSource hJump hBalance
  have hAE : (fun ω => Real.exp (θ * G t ω)) =ᵐ[P]
      (fun ω => Real.exp (θ * H ω)) := by
    filter_upwards [hHEq, hEq] with ω hHω hGω
    simp [hHω, hGω t]
  have hGInt : Integrable (fun ω => Real.exp (θ * G t ω)) P :=
    hHInt.congr hAE.symm
  let v : NNReal :=
    NNReal.mk ((t : ℝ) * X.σ ^ 2)
      (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))
  have hId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v) (gaussianReal 0 v) :=
    ⟨measurable_id.aemeasurable, by simp⟩
  have hGaussian :
      mgf id (gaussianReal 0 v) θ = Real.exp ((v : ℝ) * θ ^ 2 / 2) := by
    simpa [mgf, id] using
      (avram_a29_gaussian_haslaw_integrable_exp_exact_20261114
        (id : ℝ → ℝ) v hId θ).2
  have hv : (v : ℝ) = (t : ℝ) * X.σ ^ 2 := by simp [v]
  refine ⟨hGInt, ?_⟩
  calc
    mgf (G t) P θ =
        Real.exp ((t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by
      simpa only [mgf] using (integral_congr_ae hAE).trans hHExp
    _ = Real.exp ((v : ℝ) * θ ^ 2 / 2) := by rw [hv]; congr 1; ring
    _ = mgf id (gaussianReal 0 v) θ := hGaussian.symm
