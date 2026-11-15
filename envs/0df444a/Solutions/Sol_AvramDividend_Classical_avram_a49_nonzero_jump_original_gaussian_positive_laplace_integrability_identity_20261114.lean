-- Prove2me | solution 1 for AvramDividend.Classical.avram_a49_nonzero_jump_original_gaussian_positive_laplace_integrability_identity_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:50:51.505209+00:00
-- url     : https://prove2.me/submissions/e33a5f01-32ae-440b-b8df-151bc3d26225
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
    ∀ (t : ℝ≥0) (ht : 0 < t) (θ : ℝ), 0 < θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      mgf (G t) P θ =
        mgf id (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) θ := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t ht θ hθ
  obtain ⟨H, J, a, b, hMH, hMJ, hHEq, _, hInd,
      hProdInt, hJInt, hSource, hJump, hBalance⟩ :=
    avram_a65_original_gaussian_physical_marked_exponential_decoupling_20261114
      X hX hFinite hPositive hNu R hR t ht θ hθ
  have hFMeas : Measurable (fun ω => Real.exp (θ * H ω)) :=
    (measurable_const.mul hMH).exp
  have hJMeas : Measurable (fun ω => Real.exp (θ * J ω)) :=
    (measurable_const.mul hMJ).exp
  have hProdEq :
      (fun ω => Real.exp (θ * H ω) * Real.exp (θ * J ω)) =
        (fun ω => Real.exp (θ * (H ω + J ω))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hProd :
      Integrable (fun ω => Real.exp (θ * H ω) * Real.exp (θ * J ω)) P := by
    rw [hProdEq]
    exact hProdInt
  have hNonzero :
      ¬ ((fun ω => Real.exp (θ * J ω)) =ᵐ[P] fun _ => (0 : ℝ)) :=
    avram_a63_positive_exponential_jump_factor_nonzero_ae_20261114 J θ
  obtain ⟨hFInt, hFactors⟩ :=
    avram_a61_independent_real_product_integrability_and_mean_factorization_20261114
      (fun ω => Real.exp (θ * H ω))
      (fun ω => Real.exp (θ * J ω))
      hFMeas hJMeas hInd hProd hNonzero
  have hFactor :
      (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) =
        (∫ ω, Real.exp (θ * H ω) ∂P) *
        (∫ ω, Real.exp (θ * J ω) ∂P) := by
    calc
      (∫ ω, Real.exp (θ * (H ω + J ω)) ∂P) =
          (∫ ω, Real.exp (θ * H ω) * Real.exp (θ * J ω) ∂P) := by
            congr 1
            exact hProdEq.symm
      _ = _ := hFactors
  have hMean :=
    avram_a64_source_gaussian_mgf_from_product_and_jump_exponents_20261114
      H J θ a b ((t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2))
      hFactor hSource hJump hBalance
  have hGEq : (G t) =ᵐ[P] H := by
    filter_upwards [hEq, hHEq] with ω hGω hHω
    exact (hGω t).trans hHω.symm
  have hExpEq :
      (fun ω => Real.exp (θ * G t ω)) =ᵐ[P]
        (fun ω => Real.exp (θ * H ω)) := by
    filter_upwards [hGEq] with ω hω
    rw [hω]
  have hGInt : Integrable (fun ω => Real.exp (θ * G t ω)) P :=
    hFInt.congr hExpEq.symm
  have hGMoment :
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by
    calc
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
          (∫ ω, Real.exp (θ * H ω) ∂P) := integral_congr_ae hExpEq
      _ = _ := hMean
  let v : NNReal :=
    NNReal.mk ((t : ℝ) * X.σ ^ 2)
      (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))
  have hNormal :
      mgf id (gaussianReal 0 v) θ =
        Real.exp ((v : ℝ) * θ ^ 2 / 2) := by
    simpa [mgf] using
      (mgf_gaussianReal (show Measure.map (id : ℝ → ℝ) (gaussianReal 0 v) = gaussianReal 0 v by simp) θ)
  refine ⟨hGInt, ?_⟩
  change (∫ ω, Real.exp (θ * G t ω) ∂P) =
    mgf id (gaussianReal 0 v) θ
  rw [hGMoment, hNormal]
  congr 1
  simp only [v, NNReal.coe_mk]
  ring
