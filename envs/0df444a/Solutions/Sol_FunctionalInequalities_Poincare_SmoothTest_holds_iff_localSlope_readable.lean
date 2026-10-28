-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:09.161378+00:00
-- url     : https://prove2.me/submissions/fe613cbd-2b61-476a-9b0f-69ce603ad352

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_admissible_iff_memLp_gradient_readable
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem FunctionalInequalities.L2.center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))
/-- The mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_mean (μ : ProbabilityMeasure α) : Continuous (mean μ) :=
  continuous_id.inner continuous_const
/-- Subtracting the mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_center (μ : ProbabilityMeasure α) : Continuous (center μ) := by
  apply (continuous_id.sub ((continuous_mean μ).smul continuous_const) :
    Continuous (fun f : Lp ℝ 2 (μ : Measure α) ↦ f - mean μ f • const μ 1)).congr
  intro f
  simp only [center, ← const_smul, mul_one]
  rfl
/-- Variance is continuous in `L²`, including at constant functions. -/
theorem FunctionalInequalities.L2.continuous_variance (μ : ProbabilityMeasure α) : Continuous (variance μ) :=
  (continuous_center μ).nnnorm.pow 2
/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem FunctionalInequalities.L2.coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl
/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem FunctionalInequalities.L2.coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]
/-- The `NNReal` variance of a pointwise square-integrable function is Mathlib's real variance
converted to `NNReal`; no information is lost because pointwise variance is nonnegative. -/
theorem FunctionalInequalities.L2.variance_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    variance μ (hf.toLp f) =
      (ProbabilityTheory.variance f (μ : Measure α)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg f (μ : Measure α))]
  exact (coe_variance_eq_pointwise μ (hf.toLp f)).trans
    (ProbabilityTheory.variance_congr hf.coeFn_toLp)
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : MeasureTheory.ProbabilityMeasure E) (m : MeasureTheory.Measure E)
  [MeasureTheory.Measure.IsAddHaarMeasure m]
omit sct in
/-- Step 2: Rademacher and absolute continuity identify the two pointwise energies almost
everywhere for locally Lipschitz tests, with no integrability or density lower bound premise. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fun x ↦ apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖) := by
  filter_upwards [hν.ae_le
    (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hf m)]
    with x hx
  exact apply_eq_norm_gradient_readable f x hx
omit sct in
/-- Step 3: equality of the extended local-slope and gradient energies, also when infinite.
The lintegral keeps nonintegrable functions from acquiring a spurious zero energy. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E) := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [apply_ae_eq_norm_gradient ν m hν f hf] with x hx
  rw [hx]
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local consequence of Mathlib's `integral_nonneg` and `sq_nonneg`. -/
theorem FunctionalInequalities.Poincare.SmoothTest.energy_nonneg (μ : Measure E) (f : E → ℝ) :
    0 ≤ energy μ f := by
  exact integral_nonneg fun _ ↦ sq_nonneg _
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
private theorem FunctionalInequalities.Poincare.SmoothTest.ofReal_nnreal_mul (C : NNReal) (a : ℝ) :
    ENNReal.ofReal ((C : ℝ) * a) = (C : ENNReal) * ENNReal.ofReal a := by
  convert! ENNReal.ofReal_mul (q := a) C.2 using 1
  simp
private theorem FunctionalInequalities.Poincare.SmoothTest.variance_eq_coe_L2 {α : Type*} [MeasurableSpace α]
    (ν : ProbabilityMeasure α) (f : α → ℝ)
    (hf : MemLp f 2 (ν : Measure α)) :
    ProbabilityTheory.variance f (ν : Measure α) = (L2.variance ν (hf.toLp f) : ℝ) := by
  rw [L2.variance_toLp, Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _)]
private theorem FunctionalInequalities.Poincare.SmoothTest.integral_sq_norm_eq_norm_toLp_sq {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (ν : ProbabilityMeasure α) (f : α → V)
    (hf : MemLp f 2 (ν : Measure α)) :
    (∫ x, ‖f x‖ ^ 2 ∂(ν : Measure α)) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (hf.toLp f), MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
omit [SecondCountableTopology E] in
private theorem FunctionalInequalities.Poincare.SmoothTest.literatureEnergy_eq_ofReal_energy (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) (hg : MemLp (gradient f) 2 (ν : Measure E)) :
    Energy.LocalSlope.energy ν f = ENNReal.ofReal (energy (ν : Measure E) f) := by
  rw [Energy.LocalSlope.energy_eq_lintegral_gradient ν m hν f hf, energy,
    ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm hg.1).mp hg)
      (ae_of_all _ fun x => sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
/-- Step 5: every finite nonnegative smooth-test constant works on exactly the literature
finite-energy test domain. Use the certified approximation theorem with B equal to identity. -/
theorem solution (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) (C : NNReal) :
    FunctionalInequalities.Poincare.SmoothTest.Holds (ν : Measure E) (C : ℝ) ↔ FunctionalInequalities.Poincare.LocalSlope.Holds ν C := by
  have hgradmeas (f : E → ℝ) :=
    FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.aestronglyMeasurable_gradient f (ν : Measure E)
  constructor
  · intro h f hf
    obtain ⟨hlip, hL2, hgL2⟩ :=
      (FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_readable ν m hν f).mp hf
    obtain ⟨fs, hfs, hconv, hgconv⟩ :=
      FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2
        ν m hν (ContinuousLinearMap.id ℝ E) f hlip hL2 (by simpa using hgL2)
    have hsL2 (j : ℕ) : MemLp (fs j) 2 (ν : Measure E) := (hfs j).2.2.1
    have hgsL2 (j : ℕ) : MemLp (gradient (fs j)) 2 (ν : Measure E) := by
      simpa using (hfs j).2.2.2
    have hval := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hsL2 f hL2).mpr hconv
    have hgrad := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun j => gradient (fs j)) hgsL2 (gradient f) hgL2).mpr (by
        convert! hgconv using 1)
    have hvar : Tendsto (fun j => ProbabilityTheory.variance (fs j) (ν : Measure E)) atTop
        (𝓝 (ProbabilityTheory.variance f (ν : Measure E))) := by
      simp_rw [FunctionalInequalities.Poincare.SmoothTest.variance_eq_coe_L2 ν _ (hsL2 _), FunctionalInequalities.Poincare.SmoothTest.variance_eq_coe_L2 ν f hL2]
      exact ((NNReal.continuous_coe.comp (FunctionalInequalities.L2.continuous_variance ν)).tendsto _).comp hval
    have henergy : Tendsto (fun j => FunctionalInequalities.Poincare.SmoothTest.energy (ν : Measure E) (fs j)) atTop
        (𝓝 (FunctionalInequalities.Poincare.SmoothTest.energy (ν : Measure E) f)) := by
      simp_rw [FunctionalInequalities.Poincare.SmoothTest.energy, FunctionalInequalities.Poincare.SmoothTest.integral_sq_norm_eq_norm_toLp_sq ν _ (hgsL2 _),
        FunctionalInequalities.Poincare.SmoothTest.integral_sq_norm_eq_norm_toLp_sq ν _ hgL2]
      exact hgrad.norm.pow 2
    have hreal : ProbabilityTheory.variance f (ν : Measure E) ≤ C * FunctionalInequalities.Poincare.SmoothTest.energy (ν : Measure E) f :=
      le_of_tendsto_of_tendsto' hvar (tendsto_const_nhds.mul henergy) fun j =>
        h.variance_le ⟨(hfs j).1, hsL2 j,
          (memLp_two_iff_integrable_sq_norm (hgradmeas (fs j))).mp (hgsL2 j)⟩
    rw [← ProbabilityTheory.ofReal_variance hL2,
      FunctionalInequalities.Poincare.SmoothTest.literatureEnergy_eq_ofReal_energy ν m hν f hlip hgL2,
      ← FunctionalInequalities.Poincare.SmoothTest.ofReal_nnreal_mul C]
    exact ENNReal.ofReal_le_ofReal hreal
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    have hlip : LocallyLipschitz f := (hf.smooth'.of_le (by simp)).locallyLipschitz
    have hgL2 := (memLp_two_iff_integrable_sq_norm (hgradmeas f)).mpr hf.energy_integrable
    have hfLit := (FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_readable ν m hν f).mpr
      ⟨hlip, hf.memLp_two, hgL2⟩
    have hb := h f hfLit
    rw [← ProbabilityTheory.ofReal_variance hf.memLp_two,
      FunctionalInequalities.Poincare.SmoothTest.literatureEnergy_eq_ofReal_energy ν m hν f hlip hgL2,
      ← FunctionalInequalities.Poincare.SmoothTest.ofReal_nnreal_mul C] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.2 (FunctionalInequalities.Poincare.SmoothTest.energy_nonneg _ _))).mp hb
