-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_toLp_smul_gradient_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:59.026816+00:00
-- url     : https://prove2.me/submissions/7cd0bf62-4082-4688-be25-eb00c5ac7299

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Product rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp
end Gradient
end DifferentialTools
end
end
end

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Haar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
/-- **A Caccioppoli-type estimate for the mollified equation.** If a smooth `v` and a continuous
field `H` satisfy the weak equation `∫ Δg v = ∫ ⟪∇g, H⟫ + ∫ g v` for every smooth test `g`
supported in `tsupport χ`, then `‖χ ∇v‖ ≤ 3 ‖v ∇χ‖ + 2 ‖χ H‖` in `L²(m)`. Only the test
`g = χ² v` is used. -/
 theorem solution {χ v : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hv : ContDiff ℝ ∞ v) {H : V → V}
    (heq : ∀ g : V → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * v x ∂m =
        ∫ x, ⟪gradient g x, H x⟫ ∂m + ∫ x, g x * v x ∂m)
    (hA : MemLp (fun x => χ x • gradient v x) 2 m) (hB : MemLp (fun x => v x • gradient χ x) 2 m)
    (hC : MemLp (fun x => χ x • H x) 2 m) :
    ‖hA.toLp _‖ ≤ 3 * ‖hB.toLp _‖ + 2 * ‖hC.toLp _‖ := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv1.differentiable one_ne_zero
  -- the test function `g = χ² v`
  set g : V → ℝ := fun x => χ x * χ x * v x with hg_def
  have hg : ContDiff ℝ ∞ g := (hχ.mul hχ).mul hv
  have hgc : HasCompactSupport g := (hχc.mul_right).mul_right
  have hgs : tsupport g ⊆ tsupport χ := by
    refine closure_mono fun x hx => ?_
    simp only [Function.mem_support, hg_def] at hx ⊢
    intro h0
    exact hx (by rw [h0]; ring)
  have hgrad : ∀ x, gradient g x = (χ x * χ x) • gradient v x + (2 * (χ x * v x)) • gradient χ x := by
    intro x
    have h1 : gradient (fun y => χ y * χ y) x = χ x • gradient χ x + χ x • gradient χ x :=
      FunctionalInequalities.Analysis.BakryEmery.gradient_mul (hχd x) (hχd x)
    have h2 := FunctionalInequalities.Analysis.BakryEmery.gradient_mul (f := fun y => χ y * χ y) (g := v) (x := x) ((hχd x).mul (hχd x))
      (hvd x)
    rw [hg_def]
    refine h2.trans ?_
    rw [h1]
    module
  -- integration by parts with the constant weight
  have hibp := FunctionalInequalities.Analysis.BakryEmery.integral_mul_inner_gradient_eq_neg m (w := fun _ => (1 : ℝ)) contDiff_const
    (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgc hv1
  simp only [one_mul, gradient_fun_const, inner_zero_left, add_zero] at hibp
  have heqg := heq g hg hgc hgs
  -- the three `L²` classes and their pairings
  have hAae := hA.coeFn_toLp
  have hBae := hB.coeFn_toLp
  have hCae := hC.coeFn_toLp
  have hint : ∀ (F G : Lp V 2 m) (f g : V → V), (F : V → V) =ᵐ[m] f → (G : V → V) =ᵐ[m] g →
      Integrable (fun x => ⟪f x, g x⟫) m := fun F G f g hF hG =>
    (L2.integrable_inner F G).congr (by filter_upwards [hF, hG] with x e1 e2; rw [e1, e2])
  have hAA : ⟪hA.toLp _, hA.toLp _⟫ = ∫ x, ⟪χ x • gradient v x, χ x • gradient v x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae] with x e; rw [e])
  have hBA : ⟪hB.toLp _, hA.toLp _⟫ = ∫ x, ⟪v x • gradient χ x, χ x • gradient v x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae, hBae] with x e1 e2; rw [e1, e2])
  have hAC : ⟪hA.toLp _, hC.toLp _⟫ = ∫ x, ⟪χ x • gradient v x, χ x • H x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hAae, hCae] with x e1 e2; rw [e1, e2])
  have hBC : ⟪hB.toLp _, hC.toLp _⟫ = ∫ x, ⟪v x • gradient χ x, χ x • H x⟫ ∂m := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [hBae, hCae] with x e1 e2; rw [e1, e2])
  -- `∫ ⟪∇g, ∇v⟫ = ‖A‖² + 2 ⟪B, A⟫`
  have e1 : ∫ x, ⟪gradient g x, gradient v x⟫ ∂m =
      ‖hA.toLp _‖ ^ 2 + 2 * ⟪hB.toLp _, hA.toLp _⟫ := by
    rw [← real_inner_self_eq_norm_sq, hAA, hBA, ← integral_const_mul,
      ← integral_add (hint _ _ _ _ hAae hAae) ((hint _ _ _ _ hBae hAae).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgrad, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    ring
  -- `∫ ⟪∇g, H⟫ = ⟪A, C⟫ + 2 ⟪B, C⟫`
  have e2 : ∫ x, ⟪gradient g x, H x⟫ ∂m =
      ⟪hA.toLp _, hC.toLp _⟫ + 2 * ⟪hB.toLp _, hC.toLp _⟫ := by
    rw [hAC, hBC, ← integral_const_mul,
      ← integral_add (hint _ _ _ _ hAae hCae) ((hint _ _ _ _ hBae hCae).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgrad, inner_add_left, real_inner_smul_left, real_inner_smul_right]
    ring
  -- `∫ g v ≥ 0`
  have e3 : 0 ≤ ∫ x, g x * v x ∂m := by
    refine integral_nonneg fun x => ?_
    simp only [hg_def, Pi.zero_apply]
    nlinarith [sq_nonneg (χ x * v x)]
  -- the quadratic inequality
  have hkey : ‖hA.toLp _‖ ^ 2 + 2 * ⟪hB.toLp _, hA.toLp _⟫ +
      (⟪hA.toLp _, hC.toLp _⟫ + 2 * ⟪hB.toLp _, hC.toLp _⟫) ≤ 0 := by
    rw [← e1, ← e2, hibp]
    linarith [heqg, e3]
  have cs1 := abs_real_inner_le_norm (hB.toLp _) (hA.toLp _)
  have cs2 := abs_real_inner_le_norm (hA.toLp _) (hC.toLp _)
  have cs3 := abs_real_inner_le_norm (hB.toLp _) (hC.toLp _)
  have hA0 := norm_nonneg (hA.toLp _)
  have hB0 := norm_nonneg (hB.toLp _)
  have hC0 := norm_nonneg (hC.toLp _)
  have hsq : ‖hA.toLp _‖ ^ 2 ≤ 2 * ‖hB.toLp _‖ * ‖hA.toLp _‖ + ‖hA.toLp _‖ * ‖hC.toLp _‖ +
      2 * ‖hB.toLp _‖ * ‖hC.toLp _‖ := by
    have := neg_abs_le (⟪hB.toLp _, hA.toLp _⟫ : ℝ)
    have := neg_abs_le (⟪hA.toLp _, hC.toLp _⟫ : ℝ)
    have := neg_abs_le (⟪hB.toLp _, hC.toLp _⟫ : ℝ)
    nlinarith
  nlinarith [hsq, hA0, hB0, hC0, mul_nonneg hB0 hC0]
