-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.joint_first_derivative_of_radii_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:24:52.985457+00:00
-- url     : https://prove2.me/submissions/0e376d95-edf2-46f6-abb6-8980c964b813

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_logLaplace_jointLaw_factorization_readable
import Theorems.Thm_FunctionalInequalities_Probability_Line_laplaceMeasure_mgf_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_graph_log_integral_hasDerivAt_zero_readable

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
/-- The Laplace law is centered. -/
theorem FunctionalInequalities.Probability.Line.integral_id_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    (∫ s : ℝ, s ∂laplaceMeasure β) = 0 := by
  have h := laplaceMeasure_moment_eq_iteratedDeriv hβ 1
  change (∫ s : ℝ, s ^ 1 ∂laplaceMeasure β) = iteratedDeriv 1 (FunctionalInequalities.Probability.Line.rationalMgf β) 0 at h
  simpa only [pow_one, iteratedDeriv_one, rationalMgf_deriv_zero hβ] using h
end Moments
end
end

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff
/-- Scalar rescaling of the actual local graph derivative; no differentiability premise. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.graph_log_integral_hasDerivAt_scaled {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) (c : ℝ) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp ((c * w) * f x + ⟪z, x⟫) ∂μ))
      (c * tiltAverage μ f z) 0 := by
  have hbase := graph_log_integral_hasDerivAt_zero_readable μ hf hr hexp z hz
  have hbase' : HasDerivAt
      (fun v : ℝ => Real.log (∫ x, Real.exp (v * f x + ⟪z, x⟫) ∂μ))
      (tiltAverage μ f z) (c * (0 : ℝ)) := by simpa only [mul_zero] using hbase
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hbase'.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul c)
/-- The source copy coefficient in (111), with beta>0 and N>0 retained. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.source_copy_log_integral_hasDerivAt {n N : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (_hβ : 0 < β) (_hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp
        (w / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
          ⟪z, x⟫) ∂μ))
      (tiltAverage μ f z /
        (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)) 0 := by
  have h := graph_log_integral_hasDerivAt_scaled μ hf hr hexp z hz
    ((FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)⁻¹)
  simpa only [div_eq_mul_inv, mul_comm] using h
/-- The actual source Laplace-noise log factor has derivative zero, from its proved mean. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.source_noise_log_integral_hasDerivAt {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun w : ℝ => Real.log (∫ s : ℝ, Real.exp
      (w / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s)
        ∂FunctionalInequalities.Probability.Line.laplaceMeasure β)) 0 0 := by
  open FunctionalInequalities.Probability.Line in
  let _ : IsProbabilityMeasure (laplaceMeasure β) := isProbabilityMeasure_laplaceMeasure hβ
  have hmgf : HasDerivAt (ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β)) 0 0 := by
    have h := ProbabilityTheory.hasDerivAt_mgf (X := id)
      (FunctionalInequalities.Probability.Line.zero_mem_interior_integrableExpSet_laplaceMeasure hβ)
    simpa only [zero_mul, Real.exp_zero, mul_one, id_eq,
      FunctionalInequalities.Probability.Line.integral_id_laplaceMeasure hβ] using h
  have hval : ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β) 0 = 1 := by
    simp [ProbabilityTheory.mgf]
  have hlog : HasDerivAt (fun v : ℝ => Real.log (ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β) v)) 0 0 := by
    simpa only [hval, zero_div] using hmgf.log (by rw [hval]; norm_num)
  have hlog' : HasDerivAt (fun v : ℝ => Real.log (ProbabilityTheory.mgf id
      (FunctionalInequalities.Probability.Line.laplaceMeasure β) v)) 0
      ((0 : ℝ) / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) := by
    simpa only [zero_div] using hlog
  simpa only [Function.comp_def, ProbabilityTheory.mgf, id_eq, zero_mul] using
    hlog'.comp 0 ((hasDerivAt_id (0 : ℝ)).div_const
      (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β))
open FunctionalInequalities.Analysis.BakryEmery
open scoped Topology
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.copy_parameter_norm_le {n N : ℕ} (z : JointSpace N n) (i : Fin N) :
    ‖(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖z‖ := by
  let zi : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun j => z (some (i, j))
  have hi : ‖zi‖ ^ 2 = ∑ j : Fin n, z (some (i, j)) ^ 2 := EuclideanSpace.real_norm_sq_eq zi
  have hz : ‖z‖ ^ 2 = z none ^ 2 + ∑ k : Fin N, ∑ j : Fin n, z (some (k, j)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option, Fintype.sum_prod_type]
  have hle : (∑ j : Fin n, z (some (i, j)) ^ 2) ≤
      ∑ k : Fin N, ∑ j : Fin n, z (some (k, j)) ^ 2 :=
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
      (f := fun k : Fin N => ∑ j : Fin n, z (some (k, j)) ^ 2)
      (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg (z (some (k, j)))) (Finset.mem_univ i)
  change ‖zi‖ ≤ ‖z‖
  nlinarith [hi, hz, sq_nonneg (z none), norm_nonneg zi, norm_nonneg z]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.integrable_exp_inner_of_norm_radius {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E) {r : ℝ}
    (hexp : Integrable (fun p => Real.exp (r * ‖p‖)) ν) (q : E) (hq : ‖q‖ ≤ r) :
    Integrable (fun p => Real.exp ⟪q, p⟫) ν := by
  refine hexp.mono' ((by fun_prop : Continuous (fun p : E => Real.exp ⟪q, p⟫)).aestronglyMeasurable) ?_
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ((real_inner_le_norm q p).trans
    (mul_le_mul_of_nonneg_right hq (norm_nonneg p)))
/-- Full actual joint-law HasDerivAt identity (111), under genuine local analytic radii. -/
 theorem solution {n N : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β rJ rG : ℝ} (hβ : 0 < β) (hN : 0 < N) (_hrJ : 0 < rJ) (hrG : 0 < rG)
    (hjoint : Integrable (fun p : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n => Real.exp (rJ * ‖p‖))
      (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N))
    (hgraph : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (rG * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n) (hzero : z none = 0) (hz : ‖z‖ < min rJ rG) :
    HasDerivAt (fun w : ℝ => FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)
        (w • EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none + z))
      ((∑ i : Fin N, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j)))) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)) 0 := by
  let e0 : FunctionalInequalities.KLS.LogConcave.Suspension.JointSpace N n := EuclideanSpace.basisFun (Option (Fin N × Fin n)) ℝ none
  let noise : ℝ → ℝ := fun w => Real.log
    (∫ s : ℝ, Real.exp (w / FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * s) ∂FunctionalInequalities.Probability.Line.laplaceMeasure β)
  let copy : Fin N → ℝ → ℝ := fun i w => Real.log (∫ x, Real.exp
    (w / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N) * f x +
      ⟪(WithLp.toLp 2 fun j => z (some (i, j)) : EuclideanSpace ℝ (Fin n)), x⟫) ∂μ)
  have hzJ : ‖z‖ < rJ := hz.trans_le (min_le_left rJ rG)
  have hzG : ‖z‖ < rG := hz.trans_le (min_le_right rJ rG)
  have hsmall : ∀ᶠ w : ℝ in 𝓝 0, ‖w • e0 + z‖ < rJ := by
    have hc : Continuous (fun w : ℝ => ‖w • e0 + z‖) := by fun_prop
    exact (hc.tendsto 0).eventually_lt_const (by simpa only [zero_smul, zero_add] using hzJ)
  have hnone (w : ℝ) : (w • e0 + z) none = w := by simp [e0, hzero]
  have hcopyparam (w : ℝ) (i : Fin N) :
      (WithLp.toLp 2 fun j => (w • e0 + z) (some (i, j)) : EuclideanSpace ℝ (Fin n)) =
        WithLp.toLp 2 (fun j => z (some (i, j))) := by
    ext j
    simp [e0]
  have heq :
      (fun w : ℝ => FunctionalInequalities.Analysis.BakryEmery.logLaplace (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N) (w • e0 + z)) =ᶠ[𝓝 0]
        fun w => noise w + ∑ i : Fin N, copy i w := by
    filter_upwards [hsmall] with w hw
    have hint := FunctionalInequalities.KLS.LogConcave.Suspension.integrable_exp_inner_of_norm_radius (FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw μ f β (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β) N)
      hjoint (w • e0 + z) hw.le
    have h := FunctionalInequalities.KLS.LogConcave.Suspension.logLaplace_jointLaw_factorization_readable μ hf hβ hN (w • e0 + z) hint
    simpa only [hnone, hcopyparam, noise, copy] using h
  have hNoise : HasDerivAt noise 0 0 :=
    FunctionalInequalities.KLS.LogConcave.Suspension.source_noise_log_integral_hasDerivAt hβ
  have hCopy (i : Fin N) : HasDerivAt (copy i)
      (FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f (WithLp.toLp 2 fun j => z (some (i, j))) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)) 0 :=
    FunctionalInequalities.KLS.LogConcave.Suspension.source_copy_log_integral_hasDerivAt μ hf hβ hN hrG hgraph
      (WithLp.toLp 2 fun j => z (some (i, j)))
      ((FunctionalInequalities.KLS.LogConcave.Suspension.copy_parameter_norm_le z i).trans_lt hzG)
  have hSum : HasDerivAt (fun w : ℝ => ∑ i : Fin N, copy i w)
      (∑ i : Fin N, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j))) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hCopy i)
  have hRHS : HasDerivAt (fun w : ℝ => noise w + ∑ i : Fin N, copy i w)
      ((∑ i : Fin N, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f
        (WithLp.toLp 2 fun j => z (some (i, j)))) / (FunctionalInequalities.KLS.LogConcave.Suspension.sigma β * Real.sqrt N)) 0 := by
    simpa only [zero_add, Finset.sum_div] using hNoise.fun_add hSum
  exact hRHS.congr_of_eventuallyEq heq
