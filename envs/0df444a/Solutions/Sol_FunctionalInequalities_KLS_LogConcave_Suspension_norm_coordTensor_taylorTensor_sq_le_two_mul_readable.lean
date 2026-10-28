-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_two_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:32:43.699454+00:00
-- url     : https://prove2.me/submissions/14e754bf-0622-4dfb-aa4e-8a7bf61342b7

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_TaylorBound
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_coordTensor_taylorTensor_inner_sq_le_of_basis_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_add_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBound_jointSpace_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_copies_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_jointLaw_moments_of_laplace_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logConcave_jointLaw_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_coordTensor_taylorTensor_sq_le_of_smooth_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_sum_sq_cumulant_ge_of_entries_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_integrable_exp_mul_norm_readable
import Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_L2_integral_inner_mul_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_L2_integral_sq_eq_affine_decomposition_readable
import Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_readable
import Theorems.Thm_FunctionalInequalities_Probability_Line_laplaceMeasure_mgf_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_source_mixed_cumulant_entries_readable

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- **Isotropy from moments**: finite second moment, mean zero and `∫ ⟪u, x⟫⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.isotropic_of_moments
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) (h2 : MemLp id 2 (ν : Measure E))
    (h0 : ∫ x, x ∂(ν : Measure E) = 0)
    (hcov : ∀ u v : E, ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E) = ⟪u, v⟫) :
    Isotropic ν := by
    refine ⟨h2, h0, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right (𝕜 := ℝ)
    intro v
    rw [Covariance.operator_inner]
    rw [ProbabilityTheory.covarianceBilin_apply h2]
    simpa [h0] using hcov u v
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
end
end
end

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end

section
noncomputable section
open MeasureTheory Set
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_readable hνW hW hconv)
end
end
end

section
noncomputable section
open MeasureTheory
section Moments
open ProbabilityTheory Filter Set
open scoped Topology
/-- `0` is an interior point of the exponential-integrability set of the Laplace law. -/
theorem FunctionalInequalities.Probability.Line.zero_mem_interior_integrableExpSet_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    0 ∈ interior (integrableExpSet id (laplaceMeasure β)) := by
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Ioo_mem_nhds (by linarith : -β < 0) hβ)
  intro w hw
  exact (laplaceMeasure_mgf_readable hβ (abs_lt.mpr hw)).1
/-- Near `0` the moment generating function is the rational function `β²/(β² - w²)`. -/
theorem FunctionalInequalities.Probability.Line.laplaceMeasure_mgf_eventuallyEq {β : ℝ} (hβ : 0 < β) :
    mgf id (laplaceMeasure β) =ᶠ[𝓝 (0 : ℝ)] fun w => β ^ 2 / (β ^ 2 - w ^ 2) := by
  filter_upwards [Ioo_mem_nhds (by linarith : -β < 0) hβ] with w hw
  exact (laplaceMeasure_mgf_readable hβ (abs_lt.mpr hw)).2
/-- The `k`-th moment is the `k`-th derivative at `0` of `β²/(β² - w²)`. -/
theorem FunctionalInequalities.Probability.Line.laplaceMeasure_moment_eq_iteratedDeriv {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (∫ s : ℝ, s ^ k ∂laplaceMeasure β) =
      iteratedDeriv k (fun w : ℝ => β ^ 2 / (β ^ 2 - w ^ 2)) 0 := by
  have h := ProbabilityTheory.iteratedDeriv_mgf_zero (X := id)
    (zero_mem_interior_integrableExpSet_laplaceMeasure hβ) k
  have hd := Filter.EventuallyEq.iteratedDeriv_eq k (laplaceMeasure_mgf_eventuallyEq hβ)
  simpa only [Pi.pow_apply, id_eq] using h.symm.trans hd
/-- Every polynomial moment of the Laplace law is finite (from the rates `±β/2`). -/
theorem FunctionalInequalities.Probability.Line.integrable_pow_laplaceMeasure {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k) (laplaceMeasure β) := by
  have hhalf : 0 < β / 2 := by positivity
  have hsmall : |β / 2| < β := by rw [abs_of_pos hhalf]; linarith
  have hp := (laplaceMeasure_mgf_readable hβ hsmall).1
  have hn := (laplaceMeasure_mgf_readable (w := -(β / 2)) hβ (by simpa only [abs_neg] using hsmall)).1
  exact ProbabilityTheory.integrable_pow_of_integrable_exp_mul
    (X := id) hhalf.ne' hp hn k
/-- `G'(w) = 2β²w/(β² - w²)²` on `|w| < β`. -/
private theorem FunctionalInequalities.Probability.Line.hasDerivAt_rationalMgf {β w : ℝ} (_hβ : 0 < β) (hw : |w| < β) :
    HasDerivAt (FunctionalInequalities.Probability.Line.rationalMgf β) (FunctionalInequalities.Probability.Line.rationalMgfDeriv β w) w := by
  have hbounds := abs_lt.mp hw
  have hprod : 0 < (β - w) * (β + w) := mul_pos (by linarith) (by linarith)
  have hden : 0 < β ^ 2 - w ^ 2 := by nlinarith
  have h := (hasDerivAt_const w (β ^ 2)).div
    ((hasDerivAt_const w (β ^ 2)).sub (hasDerivAt_pow 2 w)) hden.ne'
  have h' : HasDerivAt (FunctionalInequalities.Probability.Line.rationalMgf β)
      ((0 * (β ^ 2 - w ^ 2) - β ^ 2 * (0 - 2 * w)) / (β ^ 2 - w ^ 2) ^ 2) w := by
    convert! h using 1
    simp [Pi.sub_apply]
  convert h' using 1
  dsimp [FunctionalInequalities.Probability.Line.rationalMgfDeriv]
  ring
/-- `G'(0) = 0` for `G(w) = β²/(β² - w²)`. -/
private theorem FunctionalInequalities.Probability.Line.rationalMgf_deriv_zero {β : ℝ} (hβ : 0 < β) :
    deriv (FunctionalInequalities.Probability.Line.rationalMgf β) 0 = 0 := by
  simpa [FunctionalInequalities.Probability.Line.rationalMgfDeriv] using
    (hasDerivAt_rationalMgf hβ (by simpa using hβ : |(0 : ℝ)| < β)).deriv
private theorem FunctionalInequalities.Probability.Line.hasDerivAt_rationalMgfDeriv_zero {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (FunctionalInequalities.Probability.Line.rationalMgfDeriv β) (2 / β ^ 2) 0 := by
  have hnum : HasDerivAt (fun w : ℝ => 2 * β ^ 2 * w) (2 * β ^ 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * β ^ 2)
  have hbase : HasDerivAt (fun w : ℝ => β ^ 2 - w ^ 2) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (β ^ 2)).sub (hasDerivAt_pow 2 0) using 1
    simp
  have hden : HasDerivAt (fun w : ℝ => (β ^ 2 - w ^ 2) ^ 2) 0 0 := by
    convert! hbase.pow 2 using 1
    simp
  have h := hnum.div hden (by simp [hβ.ne'])
  convert! h using 1
  field_simp [hβ.ne']
  ring
/-- `G''(0) = 2/β²` for `G(w) = β²/(β² - w²)`. -/
private theorem FunctionalInequalities.Probability.Line.rationalMgf_second_zero {β : ℝ} (hβ : 0 < β) :
    iteratedDeriv 2 (FunctionalInequalities.Probability.Line.rationalMgf β) 0 = 2 / β ^ 2 := by
  have heq : deriv (FunctionalInequalities.Probability.Line.rationalMgf β) =ᶠ[𝓝 (0 : ℝ)] FunctionalInequalities.Probability.Line.rationalMgfDeriv β := by
    filter_upwards [Ioo_mem_nhds (by linarith : -β < 0) hβ] with w hw
    exact (hasDerivAt_rationalMgf hβ (abs_lt.mpr hw)).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  exact heq.deriv_eq.trans (hasDerivAt_rationalMgfDeriv_zero hβ).deriv
/-- The Laplace law is centered. -/
theorem FunctionalInequalities.Probability.Line.integral_id_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ∂laplaceMeasure β) = 0 := by
  have h := laplaceMeasure_moment_eq_iteratedDeriv hβ 1
  change (∫ s : ℝ, s ^ 1 ∂laplaceMeasure β) = iteratedDeriv 1 (FunctionalInequalities.Probability.Line.rationalMgf β) 0 at h
  simpa only [pow_one, iteratedDeriv_one, rationalMgf_deriv_zero hβ] using h
/-- The second moment of the Laplace law is `2/β²` (the source's `σ_β² = 1 + 2/β²` adds the
unit variance of `f`). -/
theorem FunctionalInequalities.Probability.Line.integral_sq_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ^ 2 ∂laplaceMeasure β) = 2 / β ^ 2 :=
  (laplaceMeasure_moment_eq_iteratedDeriv hβ 2).trans (rationalMgf_second_zero hβ)
/-- **Mean and variance of the Laplace law**, from the local moment generating function only. -/
theorem FunctionalInequalities.Probability.Line.laplaceMeasure_moments {β : ℝ} (hβ : 0 < β) :
    Integrable (fun s : ℝ => s) (laplaceMeasure β) ∧
      Integrable (fun s : ℝ => s ^ 2) (laplaceMeasure β) ∧
      (∫ s : ℝ, s ∂laplaceMeasure β) = 0 ∧
      (∫ s : ℝ, s ^ 2 ∂laplaceMeasure β) = 2 / β ^ 2 := by
  refine ⟨?_, integrable_pow_laplaceMeasure hβ 2, integral_id_laplaceMeasure hβ,
    integral_sq_laplaceMeasure hβ⟩
  simpa only [pow_one] using integrable_pow_laplaceMeasure hβ 1
end Moments
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Line
section
/-- `σ_β² = 1 + 2/β²`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.sigma_sq {β : ℝ} (hβ : 0 < β) :
    sigma β ^ 2 = 1 + 2 / β ^ 2 := by
  unfold sigma
  rw [Real.sq_sqrt]
  positivity
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
variable {V : E → ℝ} {a b : ℝ}
theorem FunctionalInequalities.KLS.RegularPotential.logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge_readable hW hV.pos.le hV.lower)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end

section
open MeasureTheory FunctionalInequalities.Probability.Line
section
open FunctionalInequalities.Analysis.BakryEmery in
/-- **The joint law is log-concave** under (110) (BKL p. 28, "Then `W_N` is convex"): (109) from
`jointLaw_eq_tilted` and convexity of `W_N` from `logConcave_jointLaw_of_eq_tilted`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ}
    (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) :=
  logConcave_jointLaw_of_eq_tilted_readable V f hβ hV hf hVa hfM hN
    (jointLaw_eq_tilted_readable V f hβ hV.continuous.measurable hf.continuous.measurable hint) h
end
end

section
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
section
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff
open FunctionalInequalities.Analysis.BakryEmery
open scoped Topology
open FunctionalInequalities
open scoped ContDiff
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
set_option autoImplicit false
open Filter Set
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
open scoped RealInnerProductSpace ContDiff Topology
theorem FunctionalInequalities.KLS.LogConcave.Suspension.cumulant_jointLaw_none_entries {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}
    (hβ : 0 < β) (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a) {d : ℕ} (hd : 1 ≤ d) (I : Fin d → Fin N) (J : Fin d → Fin n) :
    cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
        (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (I k, J k)) 1) =
      if ∀ k k', I k = I k' then
        (d.factorial : ℝ) / (sigma β * Real.sqrt N) *
          taylorTensor (hV.law : Measure _) f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
      else 0 := by
  exact source_mixed_cumulant_entries_readable hN V hV hβ hf hfM h110 hd I J
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
section
/-- **Isotropy of the joint law** (BKL p. 28), with the Laplace data discharged by
`laplaceMeasure_moments`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.isotropic_jointLaw {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) {β : ℝ} (hβ : 0 < β) :
    FunctionalInequalities.KLS.Isotropic
      (⟨jointLaw μ f β (sigma β) N,
        isProbabilityMeasure_jointLaw_of_pos μ hf hβ (sigma β) N⟩ :
        ProbabilityMeasure (JointSpace N n)) := by
  have : IsProbabilityMeasure (laplaceMeasure β) := isProbabilityMeasure_laplaceMeasure hβ
  obtain ⟨hη1, hη2, hη0, hηv⟩ := laplaceMeasure_moments hβ
  have h := jointLaw_moments_of_laplace_readable hN μ hμ2 hμ0 hμcov hf hf2 hf0 hf1 hfx
    hβ hη1 hη2 hη0 hηv
  exact FunctionalInequalities.KLS.isotropic_of_moments
    (⟨jointLaw μ f β (sigma β) N,
      isProbabilityMeasure_jointLaw_of_pos μ hf hβ (sigma β) N⟩ :
      ProbabilityMeasure (JointSpace N n)) h.1 h.2.1 h.2.2
end
end
end

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.r7_source_energy_limit {T b : ℝ} {d : ℕ} (hb : 0 < b) (hd : 2 ≤ d)
    (hβbound : ∀ β : ℝ, 0 < β → T ≤ (sigma β) ^ 2 * b / (d.factorial : ℝ) ^ 2) :
    T ≤ b / (d.factorial : ℝ) ^ 2 := by
  have hfac_nat : 2 ≤ d.factorial := by simpa using Nat.factorial_le hd
  have hfac : (2 : ℝ) ≤ (d.factorial : ℝ) := by exact_mod_cast hfac_nat
  have hα : 0 < b / (d.factorial : ℝ) ^ 2 := div_pos hb (pow_pos (by linarith) 2)
  let α : ℝ := b / (d.factorial : ℝ) ^ 2
  by_contra hnot
  have hgap : 0 < T - α := sub_pos.mpr (lt_of_not_ge hnot)
  let β : ℝ := Real.sqrt (4 * α / (T - α))
  have hratio : 0 < 4 * α / (T - α) := by change 0 < 4 * (b / (d.factorial : ℝ) ^ 2) / (T - α); positivity
  have hβ : 0 < β := Real.sqrt_pos.mpr hratio
  have hβsq : β ^ 2 = 4 * α / (T - α) := Real.sq_sqrt hratio.le
  have hproduct : β ^ 2 * (T - α) = 4 * α := (eq_div_iff hgap.ne').mp hβsq
  have hextra : 2 * α / β ^ 2 < T - α := by
    apply (div_lt_iff₀ (pow_pos hβ 2)).2
    nlinarith [hproduct]
  have hbβ : T ≤ sigma β ^ 2 * α := by
    simpa only [α, mul_div_assoc] using hβbound β hβ
  rw [sigma_sq hβ] at hbβ
  have heq : (1 + 2 / β ^ 2) * α = α + 2 * α / β ^ 2 := by ring
  rw [heq] at hbβ
  linarith
set_option maxHeartbeats 800000 in
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.r7_beta_energy_bound {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hf2 : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) {β : ℝ} (hβ : 0 < β) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      sigma β ^ 2 * b / (d.factorial : ℝ) ^ 2 := by
  classical
  have hM : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hfM 0)
  obtain ⟨N, hN, h110⟩ := exists_copies_readable hV.pos hβ.le hM
  let ν : ProbabilityMeasure (JointSpace N n) :=
    ⟨jointLaw (hV.law : Measure _) f β (sigma β) N,
      isProbabilityMeasure_jointLaw_of_pos (hV.law : Measure _) hf.continuous.measurable hβ (sigma β) N⟩
  have hisoν : KLS.Isotropic ν := isotropic_jointLaw hN (hV.law : Measure _)
    hiso.memLp_two hiso.mean_zero hiso.integral_inner_mul_inner
    hf.continuous.measurable hf2 hf0 hf1 hfx hβ
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlcν : KLS.LogConcave ν := logConcave_jointLaw V f hβ hV2 hf
    hV.lower hfM h110 hV.integrable_exp_neg ν.prop
  have hhigh := cumulantBound_jointSpace_readable hcb hisoν hlcν (EuclideanSpace.single none 1)
  have hhigh' : (∑ K : Fin d → Option (Fin N × Fin n),
      cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
        (Fin.cons (EuclideanSpace.single none 1) fun k => EuclideanSpace.single (K k) 1) ^ 2) ≤ b := by
    simpa only [ν, ProbabilityMeasure.coe_mk, EuclideanSpace.basisFun_apply, PiLp.norm_single, norm_one,
      one_pow, mul_one] using hhigh
  have hσ : 0 < sigma β := Real.sqrt_pos.mpr (by positivity)
  have hlow := sum_sq_cumulant_ge_of_entries_readable hN
    (jointLaw (hV.law : Measure _) f β (sigma β) N) (hV.law : Measure _) f hσ hd
    (fun I J => cumulant_jointLaw_none_entries hN V hV hβ hf hfM h110 hd I J)
  have hbound := hlow.trans hhigh'
  have hfac : 0 < (d.factorial : ℝ) ^ 2 := by positivity
  have hσsq : 0 < sigma β ^ 2 := pow_pos hσ 2
  have hbound' : (d.factorial : ℝ) ^ 2 *
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤ b * sigma β ^ 2 := by
    apply (div_le_iff₀ hσsq).mp
    simpa only [div_mul_eq_mul_div] using hbound
  apply (le_div_iff₀ hfac).mpr
  nlinarith only [hbound']
/-- **BKL (113) for `f ∈ C²` with bounded Hessian satisfying (108)**: under `CumulantBound d b`, for an
isotropic regular law, `|T_d f|² ≤ b/(d!)²`. For each `β > 0` a copy number `N` is chosen by (110); the
joint law is isotropic and log-concave, (112) and the Hilbert–Schmidt step give
`(d!)²/σ_β² |T_d f|² ≤ b`, and `β → ∞`. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_cumulantBound {d : ℕ} (hd : 2 ≤ d) {b : ℝ}
    (hb : 0 < b) (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hf2 : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 := by
  apply r7_source_energy_limit hb hd
  intro β hβ
  exact r7_beta_energy_bound (by omega) hcb V hV hiso hf hfM hf2 hf0 hf1 hfx hβ
open scoped ContDiff
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.L2
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
section MeasurableSpace
variable {A : Type*}
variable [MeasurableSpace A]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_sq_eq_norm_sq
    (μ : Measure A) {g : A → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ^ 2 ∂μ) = (eLpNorm g 2 μ).toReal ^ 2 := by
  let G : Lp ℝ 2 μ := hg.toLp g
  have hG : G =ᵐ[μ] g := hg.coeFn_toLp
  calc
    (∫ x, g x ^ 2 ∂μ) = ∫ x, (G x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      rw [hx]
    _ = ∫ x, ⟪G x, G x⟫ ∂μ := by
      congr 1
      funext x
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ⟪G, G⟫ := (MeasureTheory.L2.inner_def G G).symm
    _ = ‖G‖ ^ 2 := real_inner_self_eq_norm_sq G
    _ = (eLpNorm g 2 μ).toReal ^ 2 := by rw [Lp.norm_toLp]
end MeasurableSpace
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.coeffs_add {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ (fun x => f x + g x) d) =
      coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d) +
        coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d) := by
  rw [taylorTensor_add_readable μ hexp hf hg]
  ext J
  simp [coordTensor_apply]
/-- **BKL (113) for every `f ∈ L²(μ)` orthogonal to the affine functions**, under `CumulantBound d b`:
the smooth case `norm_coordTensor_taylorTensor_sq_le_of_cumulantBound` extended by density. -/
theorem FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_orthogonal {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b)
    (hcb : CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 :=
  norm_coordTensor_taylorTensor_sq_le_of_smooth_readable hb.le V hV hiso
    (fun _g hg ⟨_M, hM⟩ hg2 hg0 hg1 hgx =>
      norm_coordTensor_taylorTensor_sq_le_of_cumulantBound hd hb hcb V hV hiso hg hM hg2 hg0 hg1 hgx)
    hf hf0 hfx
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave.Suspension
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.taylorTensor_constant_zero {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (c : ℝ) (hd : 1 ≤ d) : taylorTensor μ (fun _ => c) d = 0 := by
  have hprob (z : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (expTilt μ z) := by
    have hint : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      refine (hexp ‖z‖).mono'
        ((by fun_prop : Continuous (fun x => Real.exp ⟪z, x⟫)).aestronglyMeasurable) ?_
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    exact isProbabilityMeasure_tilted hint
  have hAvg : tiltAverage μ (fun _ => c) = fun _ => c := by
    funext z
    let _ : IsProbabilityMeasure (expTilt μ z) := hprob z
    simp [tiltAverage]
  unfold taylorTensor
  rw [hAvg, iteratedFDeriv_const_of_ne (by omega : d ≠ 0)]
  ext h
  simp
/-- **BKL Proposition 7.1, (107).** Exact original mathematical header. -/
theorem solution {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b)
    (hcb : FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d b) {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : FunctionalInequalities.KLS.RegularPotential V a b') (hiso : FunctionalInequalities.KLS.Isotropic hV.law)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 (hV.law : Measure _)) :
    ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by
  classical
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := hV.law
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let c : ℝ := ∫ x, f x ∂μ
  let co : Fin n → ℝ := fun j => ∫ x, ⟪e j, x⟫ * f x ∂μ
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 co
  let l : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪v, x⟫
  let q : EuclideanSpace ℝ (Fin n) → ℝ := FunctionalInequalities.L2.affineOrthPart μ f
  let A : (EuclideanSpace ℝ (Fin n) → ℝ) → FunctionalInequalities.Analysis.Tensor.Coord n d :=
    fun g => FunctionalInequalities.Analysis.Tensor.coordTensor e (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ g d)
  let B : ℝ := b / (d.factorial : ℝ) ^ 2
  have hB : 0 ≤ B := div_nonneg hb.le (sq_nonneg _)
  have hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ := hV.integrable_exp_mul_norm_readable
  have hq2 : MemLp q 2 μ := FunctionalInequalities.L2.memLp_affineOrthPart_readable μ hiso.memLp_two hf
  have hq0 : ∫ x, q x ∂μ = 0 := FunctionalInequalities.L2.integral_affineOrthPart_readable μ hiso.memLp_two hiso.mean_zero hf
  have hqorth : ∀ u, ∫ x, ⟪u, x⟫ * q x ∂μ = 0 :=
    FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_readable μ hiso.memLp_two hiso.mean_zero hiso.integral_inner_mul_inner hf
  have hqbound : ‖A q‖ ^ 2 ≤ B * (eLpNorm q 2 μ).toReal ^ 2 :=
    FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_orthogonal hd hb hcb V hV hiso hq2 hq0 hqorth
  have hl2 : MemLp l 2 μ := by
    simpa only [l, μ, Function.comp_def, id_eq, innerSL_apply_apply] using
      (innerSL ℝ v).comp_memLp' hiso.memLp_two
  have hlbound : ‖A l‖ ^ 2 ≤ B * ‖v‖ ^ 2 :=
    FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_readable μ hexp e
      (hcb n hV.law hiso hV.logConcave_law) v
  have hvnorm : ‖v‖ ^ 2 = ∑ j, co j ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have hrepr (x : EuclideanSpace ℝ (Fin n)) :
      ⟪v, x⟫ = ∑ j, co j * ⟪e j, x⟫ := by
    simpa only [e, EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real, v] using
      (e.sum_inner_mul_inner v x).symm
  have hdecomp : (fun x => (c + l x) + q x) = f := by
    funext x
    simp only [q, l, hrepr, c, co, FunctionalInequalities.L2.affineOrthPart, e]
    ring
  have hc2 : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => c) 2 μ := memLp_const c
  have hcl2 : MemLp (fun x => c + l x) 2 μ := hc2.add hl2
  have hconst : A (fun _ => c) = 0 := by
    dsimp [A]
    rw [FunctionalInequalities.KLS.LogConcave.Suspension.taylorTensor_constant_zero μ hexp c (by omega)]
    ext J
    simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply]
  have hAl : A (fun x => c + l x) = A l := by
    have ht := FunctionalInequalities.KLS.LogConcave.Suspension.coeffs_add μ hexp hc2 hl2 (d := d)
    change A (fun x => c + l x) = A (fun _ => c) + A l at ht
    rw [hconst, zero_add] at ht
    exact ht
  have hAf : A f = A l + A q := by
    have ht := FunctionalInequalities.KLS.LogConcave.Suspension.coeffs_add μ hexp hcl2 hq2 (d := d)
    rw [hdecomp] at ht
    change A f = A (fun x => c + l x) + A q at ht
    rw [hAl] at ht
    exact ht
  have hpyth := FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_readable μ hiso.memLp_two hiso.mean_zero
    hiso.integral_inner_mul_inner hf
  have henergy : ‖v‖ ^ 2 + ∫ x, q x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
    change ‖v‖ ^ 2 + ∫ x, FunctionalInequalities.L2.affineOrthPart μ f x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ
    rw [hvnorm]
    dsimp [co, e]
    linarith [sq_nonneg (∫ x, f x ∂μ)]
  have hqnorm : (eLpNorm q 2 μ).toReal ^ 2 = ∫ x, q x ^ 2 ∂μ :=
    (FunctionalInequalities.KLS.LogConcave.Suspension.integral_sq_eq_norm_sq μ hq2).symm
  have hfnorm : (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ :=
    (FunctionalInequalities.KLS.LogConcave.Suspension.integral_sq_eq_norm_sq μ hf).symm
  have htri : ‖A f‖ ≤ ‖A l‖ + ‖A q‖ := by rw [hAf]; exact norm_add_le _ _
  have htwonorm : ‖A f‖ ^ 2 ≤ 2 * (‖A l‖ ^ 2 + ‖A q‖ ^ 2) := by
    nlinarith [norm_nonneg (A f), norm_nonneg (A l), norm_nonneg (A q),
      sq_nonneg (‖A l‖ - ‖A q‖)]
  rw [hqnorm] at hqbound
  change ‖A f‖ ^ 2 ≤ 2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 μ).toReal ^ 2
  rw [hfnorm]
  calc
    ‖A f‖ ^ 2 ≤ 2 * (‖A l‖ ^ 2 + ‖A q‖ ^ 2) := htwonorm
    _ ≤ 2 * (B * ‖v‖ ^ 2 + B * ∫ x, q x ^ 2 ∂μ) := by gcongr
    _ = 2 * B * (‖v‖ ^ 2 + ∫ x, q x ^ 2 ∂μ) := by ring
    _ ≤ 2 * B * (∫ x, f x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left henergy (mul_nonneg (by norm_num) hB)
    _ = _ := by dsimp [B]; ring
