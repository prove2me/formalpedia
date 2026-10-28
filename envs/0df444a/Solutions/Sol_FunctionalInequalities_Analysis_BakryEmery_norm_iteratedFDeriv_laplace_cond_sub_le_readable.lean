-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:21.603425+00:00
-- url     : https://prove2.me/submissions/9b4c2d04-3fe2-4b0e-8b4d-47c62c9eef7d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Truncation

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Norm moments of every order from one positive exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_norm_pow_of_exp_cond (μ : Measure E) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ d) μ := by
  have hneg : Integrable (fun x : E => Real.exp (-r * ‖x‖)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hr.le) (norm_nonneg x))
  simpa only [abs_norm] using
    ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul hr.ne' hexp hneg d
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.norm_prod_inner_le_cond (d : ℕ) (h : Fin d → E) (x : E) :
    ‖∏ j, ⟪x, h j⟫‖ ≤ ‖x‖ ^ d * ∏ j, ‖h j‖ := by
  rw [norm_prod]
  calc
    ∏ j, ‖⟪x, h j⟫‖ ≤ ∏ j, ‖x‖ * ‖h j‖ := by
      apply Finset.prod_le_prod
      · intro j _; exact norm_nonneg _
      · intro j _; exact norm_inner_le_norm _ _
    _ = ‖x‖ ^ d * ∏ j, ‖h j‖ := by rw [Finset.prod_mul_distrib]; simp
omit [FiniteDimensional ℝ E] in
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_prod_inner_cond (μ : Measure E) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ)
    (h : Fin d → E) : Integrable (fun x : E => ∏ j, ⟪x, h j⟫) μ :=
  ((integrable_norm_pow_of_exp_cond μ hr hexp d).mul_const (∏ j, ‖h j‖)).mono' (by fun_prop)
    (ae_of_all _ fun x => norm_prod_inner_le_cond d h x)
/-- Operator-norm distance between the moment tensors of `ν[|s]` and `ν`. -/
theorem solution (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ)
    {s : Set E} (hs : MeasurableSet s) (hs0 : ν s ≠ 0) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|s])) 0 -
        iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0‖ ≤
      |((ν s)⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν := by
  have : IsProbabilityMeasure (ν[|s]) := cond_isProbabilityMeasure hs0
  have hexp' : Integrable (fun x => Real.exp (r * ‖x‖)) (ν[|s]) :=
    (hexp.restrict (s := s)).smul_measure (ENNReal.inv_ne_top.2 hs0)
  have hpow := FunctionalInequalities.Analysis.BakryEmery.integrable_norm_pow_of_exp_cond ν hr hexp d
  have hM : 0 ≤ ∫ x, ‖x‖ ^ d ∂ν := integral_nonneg fun x => by positivity
  have he : 0 ≤ ∫ x in sᶜ, ‖x‖ ^ d ∂ν := integral_nonneg fun x => by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun h => ?_
  rw [sub_apply, FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero (ν[|s]) hr hexp' d h,
    FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero ν hr hexp d h]
  have hint := FunctionalInequalities.Analysis.BakryEmery.integrable_prod_inner_cond ν hr hexp d h
  have hP : 0 ≤ ∏ j, ‖h j‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
  have hcond : ∫ x, ∏ j, ⟪x, h j⟫ ∂(ν[|s]) =
      ((ν s)⁻¹).toReal * ∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν := by
    simp only [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
  have hsplit := integral_add_compl hs hint
  have hbound : ∀ᵐ x ∂ν, ‖∏ j, ⟪x, h j⟫‖ ≤ ‖x‖ ^ d * ∏ j, ‖h j‖ :=
    ae_of_all _ fun x => FunctionalInequalities.Analysis.BakryEmery.norm_prod_inner_le_cond d h x
  have hA : ‖∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ (∫ x, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := by
    calc
      ‖∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ ∫ x in s, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂ν :=
        norm_integral_le_of_norm_le (hpow.mul_const _).restrict (ae_restrict_of_ae hbound)
      _ ≤ ∫ x, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂ν :=
        setIntegral_le_integral (hpow.mul_const _) (ae_of_all _ fun x => by positivity)
      _ = (∫ x, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := integral_mul_const _ _
  have hA' : ‖∫ x in sᶜ, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ (∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := by
    calc
      ‖∫ x in sᶜ, ∏ j, ⟪x, h j⟫ ∂ν‖ ≤ ∫ x in sᶜ, ‖x‖ ^ d * ∏ j, ‖h j‖ ∂ν :=
        norm_integral_le_of_norm_le (hpow.mul_const _).restrict (ae_restrict_of_ae hbound)
      _ = (∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := integral_mul_const _ _
  rw [hcond, ← hsplit]
  set c := ((ν s)⁻¹).toReal
  set A := ∫ x in s, ∏ j, ⟪x, h j⟫ ∂ν
  set A' := ∫ x in sᶜ, ∏ j, ⟪x, h j⟫ ∂ν
  calc
    ‖c * A - (A + A')‖ = ‖(c - 1) * A - A'‖ := by congr 1; ring
    _ ≤ ‖(c - 1) * A‖ + ‖A'‖ := norm_sub_le _ _
    _ = |c - 1| * ‖A‖ + ‖A'‖ := by rw [norm_mul, Real.norm_eq_abs]
    _ ≤ |c - 1| * ((∫ x, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖) + (∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) hA'
    _ = (|c - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν) * ∏ j, ‖h j‖ := by ring
