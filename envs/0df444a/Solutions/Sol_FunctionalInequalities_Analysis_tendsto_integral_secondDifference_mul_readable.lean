-- Prove2me | solution 1 for FunctionalInequalities.Analysis.tendsto_integral_secondDifference_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:41.457872+00:00
-- url     : https://prove2.me/submissions/43d638ae-12df-44a7-9664-f272b7f01970

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section LT12D7FatouSecondDifference
open MeasureTheory Set Filter
open scoped Topology
private lemma FunctionalInequalities.Analysis.secondDifference_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Tendsto (fun t : ℝ => (f t + f (-t) - 2 * f 0) / t ^ 2)
      (𝓝[>] 0) (𝓝 (iteratedDeriv 2 f 0)) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 2) hf).tendsto_div_nhds_zero
  have hn := h.comp (show Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) by
    simpa using continuous_neg.tendsto (0 : ℝ))
  have H := ((h.add hn).add_const (iteratedDeriv 2 f 0)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [zero_add] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp
  simp only [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
    taylor_within_zero_eval, iteratedDerivWithin_univ, sub_zero]
  norm_num
  field_simp
  ring
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.directional_second_derivative {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) (v x : E) :
    fderiv ℝ (fun y => fderiv ℝ ψ y v) x v =
      iteratedFDeriv ℝ 2 ψ x (fun _ => v) := by
  rw [fderiv_clm_apply
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
    (differentiableAt_const v)]
  simp [iteratedFDeriv_two_apply]
end NormedSpace
section InnerProduct
variable [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.reflected_convolution_eq (u ψ : E → ℝ) (z : E) :
    convolution (fun y => u (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume z =
      ∫ x, u (x - z) * ψ x := by
  have h := integral_sub_left_eq_self
    (fun y => u (-y) * ψ (z - y)) (volume : Measure E) z
  simpa only [convolution_def, ContinuousLinearMap.mul_apply',
    neg_sub, sub_sub_cancel] using h.symm
private lemma FunctionalInequalities.Analysis.reflected_convolution_hasDerivAt {u ψ : E → ℝ}
    (hu : Continuous u) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (v : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        convolution (fun y => u (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (s • v))
      (convolution (fun y => u (-y)) (fun x => fderiv ℝ ψ x v)
        (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)) t := by
  have hi : LocallyIntegrable (fun y => u (-y)) (volume : Measure E) :=
    (hu.comp continuous_neg).locallyIntegrable
  have h :=
    (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hi hψ (t • v)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
  simp only [one_smul] at h
  exact h.congr_deriv
    (convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hi
      (hψc.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) (t • v) v)
private lemma FunctionalInequalities.Analysis.integral_secondDifference_eq {u χ : E → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : E) (t : ℝ) :
    (∫ x, (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x) =
      ((∫ x, u (x + t • v) * χ x) + (∫ x, u (x - t • v) * χ x) -
        2 * (∫ x, u x * χ x)) / t ^ 2 := by
  have hpc : Continuous (fun x => u (x + t • v) * χ x) :=
    (hu.comp (continuous_id.add continuous_const)).mul hχ
  have hmc : Continuous (fun x => u (x - t • v) * χ x) :=
    (hu.comp (continuous_id.sub continuous_const)).mul hχ
  have hp : Integrable (fun x => u (x + t • v) * χ x) (volume : Measure E) :=
    hpc.integrable_of_hasCompactSupport hχc.mul_left
  have hm : Integrable (fun x => u (x - t • v) * χ x) (volume : Measure E) :=
    hmc.integrable_of_hasCompactSupport hχc.mul_left
  have hz : Integrable (fun x => u x * χ x) (volume : Measure E) :=
    (hu.mul hχ).integrable_of_hasCompactSupport hχc.mul_left
  have hsum :
      Integrable (fun x => u (x + t • v) * χ x + u (x - t • v) * χ x)
        (volume : Measure E) := hp.add hm
  have htwo : Integrable (fun x => 2 * (u x * χ x)) (volume : Measure E) :=
    hz.const_mul 2
  calc
    _ = ∫ x, ((u (x + t • v) * χ x + u (x - t • v) * χ x) -
        2 * (u x * χ x)) / t ^ 2 := by
      apply integral_congr_ae
      exact .of_forall (fun x => by ring)
    _ = _ := by
      rw [integral_div, integral_sub hsum htwo,
        integral_add hp hm, integral_const_mul]
/-- **Second difference quotients converge to the distributional second derivative** (weak Letwin route): for continuous `u` and `χ ∈ C²` with compact support,
`∫ (u(x + t v) + u(x − t v) − 2 u(x)) / t² · χ(x) dx → ∫ u(x) ∂²_v χ(x) dx` as `t → 0⁺`. -/
theorem solution
    {u : E → ℝ} (hu : Continuous u) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (v : E) :
    Tendsto (fun t : ℝ => ∫ x, (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x)
      (𝓝[>] 0) (𝓝 (∫ x, u x * iteratedFDeriv ℝ 2 χ x (fun _ => v))) := by
  let F : ℝ → ℝ := fun t =>
    convolution (fun y => u (-y)) χ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)
  let ψ : E → ℝ := fun x => fderiv ℝ χ x v
  have hi : LocallyIntegrable (fun y => u (-y)) (volume : Measure E) :=
    (hu.comp continuous_neg).locallyIntegrable
  have hF : ContDiff ℝ 2 F :=
    (hχc.contDiff_convolution_right (n := 2)
      (ContinuousLinearMap.mul ℝ ℝ) hi hχ).comp (contDiff_id.smul contDiff_const)
  have hψ : ContDiff ℝ 1 ψ :=
    (hχ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hψc : HasCompactSupport ψ := hχc.fderiv_apply ℝ v
  have hd : deriv F = fun t =>
      convolution (fun y => u (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v) := by
    funext t
    exact (FunctionalInequalities.Analysis.reflected_convolution_hasDerivAt hu (hχ.of_le (by norm_num))
      hχc v t).deriv
  have hdd : iteratedDeriv 2 F 0 =
      ∫ x, u x * iteratedFDeriv ℝ 2 χ x (fun _ => v) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd,
      (FunctionalInequalities.Analysis.reflected_convolution_hasDerivAt hu hψ hψc v 0).deriv]
    simp only [zero_smul, convolution_def, ContinuousLinearMap.mul_apply', zero_sub]
    change (∫ x, u (-x) * fderiv ℝ (fun y => fderiv ℝ χ y v) (-x) v) = _
    simp_rw [FunctionalInequalities.Analysis.directional_second_derivative hχ]
    exact integral_neg_eq_self
      (fun x => u x * iteratedFDeriv ℝ 2 χ x (fun _ => v)) volume
  have heq (t : ℝ) :
      (∫ x, (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x) =
        (F t + F (-t) - 2 * F 0) / t ^ 2 := by
    rw [FunctionalInequalities.Analysis.integral_secondDifference_eq hu hχ.continuous hχc]
    dsimp only [F]
    simp only [FunctionalInequalities.Analysis.reflected_convolution_eq, neg_smul, sub_neg_eq_add,
      zero_smul, sub_zero]
    ring
  have H := FunctionalInequalities.Analysis.secondDifference_tendsto hF
  rw [hdd] at H
  exact H.congr' (.of_forall fun t => (heq t).symm)
