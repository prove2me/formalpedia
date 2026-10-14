-- Prove2me | solution 1 for DbarRegularity.integral_norm_sq_le_integral_norm_fderiv_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:09:24.6902+00:00
-- url     : https://prove2.me/submissions/cddf5e51-c7e8-4c1b-8111-21b4e0ea046e

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_DbarRegularity_integral_norm_sq_le_of_tsupport_subset_ball



namespace DbarRegularity

open MeasureTheory Metric Set

/-- L² Poincaré inequality in the real direction on the plane: a `C¹` map `φ : ℂ → E` with support
in the disc `B_R(0)` satisfies `∫ ‖φ‖² ≤ 4R² ∫ ‖φ_s‖²`, where `φ_s = fderiv ℝ φ z 1`. -/
theorem integral_norm_sq_le_integral_norm_fderiv_one_sq_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ) (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ)
    (hsupp : tsupport φ ⊆ ball 0 R) :
    ∫ z, ‖φ z‖ ^ 2 ≤ 4 * R ^ 2 * ∫ z, ‖fderiv ℝ φ z 1‖ ^ 2 := by
  set e := Complex.measurableEquivRealProd
  have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hsym : ∀ p : ℝ × ℝ, e.symm p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    intro p; apply Complex.ext <;> simp [e, Complex.measurableEquivRealProd_symm_apply]
  have hcpt : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hzero : ∀ z, z ∉ closedBall (0 : ℂ) R → φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => hz (ball_subset_closedBall (hsupp hm))
  have hdzero : ∀ z, z ∉ closedBall (0 : ℂ) R → fderiv ℝ φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm =>
      hz (ball_subset_closedBall (hsupp (tsupport_fderiv_subset ℝ hm)))
  have hF : Integrable (fun z => ‖φ z‖ ^ 2) := by
    apply (by have := hφ.continuous; fun_prop : Continuous fun z => ‖φ z‖ ^ 2)
      |>.integrable_of_hasCompactSupport
    exact HasCompactSupport.intro hcpt fun z hz => by simp [hzero z hz]
  have hH : Integrable (fun z => ‖fderiv ℝ φ z 1‖ ^ 2) := by
    have hc := hφ.continuous_fderiv (by norm_num)
    apply (by fun_prop : Continuous fun z => ‖fderiv ℝ φ z 1‖ ^ 2)
      |>.integrable_of_hasCompactSupport
    exact HasCompactSupport.intro hcpt fun z hz => by simp [hdzero z hz]
  have hF2 : Integrable (fun p : ℝ × ℝ => ‖φ (e.symm p)‖ ^ 2) (volume.prod volume) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hF
  have hH2 : Integrable (fun p : ℝ × ℝ => ‖fderiv ℝ φ (e.symm p) 1‖ ^ 2) (volume.prod volume) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hH
  rw [← hmp.integral_comp' (fun z => ‖φ z‖ ^ 2),
    ← hmp.integral_comp' (fun z => ‖fderiv ℝ φ z 1‖ ^ 2)]
  rw [integral_prod_symm _ hF2, integral_prod_symm _ hH2, ← integral_const_mul]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => integral_nonneg
    fun _ => by positivity) (hH2.integral_prod_right.const_mul _)
  refine Filter.Eventually.of_forall fun t => ?_
  simp only [hsym]
  -- the slice through height `t`
  set c : ℝ → ℂ := fun s => (s : ℂ) + (t : ℂ) * Complex.I
  have hc : ContDiff ℝ 1 c := ContDiff.add Complex.ofRealCLM.contDiff contDiff_const
  have hcd : ∀ s, HasDerivAt c 1 s := fun s => by
    have := ((hasDerivAt_id s).ofReal_comp).add_const ((t : ℂ) * Complex.I)
    convert this using 1 <;> first | rfl | simp [c]
  have hsl : ContDiff ℝ 1 (φ ∘ c) := hφ.comp hc
  have hslsupp : tsupport (φ ∘ c) ⊆ ball 0 R := by
    refine (tsupport_comp_subset_preimage φ hc.continuous).trans fun s hs => ?_
    have := hsupp hs
    rw [mem_ball, dist_zero_right] at this ⊢
    calc ‖s‖ = |(c s).re| := by simp [c]
      _ ≤ ‖c s‖ := Complex.abs_re_le_norm _
      _ < R := this
  have hderiv : ∀ s, deriv (φ ∘ c) s = fderiv ℝ φ (c s) 1 := fun s =>
    (((hφ.differentiable one_ne_zero) (c s)).hasFDerivAt.comp_hasDerivAt s (hcd s)).deriv
  have := integral_norm_sq_le_of_tsupport_subset_ball R (φ ∘ c) hsl hslsupp
  simp only [hderiv, Function.comp] at this
  exact this

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ) (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ)
    (hsupp : tsupport φ ⊆ ball 0 R) :
    ∫ z, ‖φ z‖ ^ 2 ≤ 4 * R ^ 2 * ∫ z, ‖fderiv ℝ φ z 1‖ ^ 2 :=
  integral_norm_sq_le_integral_norm_fderiv_one_sq_aux R φ hφ hsupp
