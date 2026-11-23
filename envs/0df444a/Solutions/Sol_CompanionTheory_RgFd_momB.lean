-- Prove2me | solution 1 for CompanionTheory.RgFd.momB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:03.077617+00:00
-- url     : https://prove2.me/submissions/ee9cf468-94e4-42c1-aa21-375e4b51f853

import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomB
import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomentRecursion_MomStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.RgFd
namespace CompanionTheory.RgFd
theorem _root_.solution : MomB := by
  intro I _ α β c hα hβ hc
  refine ⟨(Measure.pi fun _ : I => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
    fun y => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|)), fun y => ∏ i, Real.exp (-β i * |y i|), by fun_prop,
    fun y => ⟨Finset.prod_pos fun i _ => Real.exp_pos _, Finset.prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ =>
      Real.exp_le_one_iff.2 (by have := hβ i; have := abs_nonneg (y i); nlinarith)⟩, fun t => ?_⟩
  have hp : ∀ i, 0 < α i + t * β i := fun i => by have := hα i; have := hβ i; positivity
  have e1 : ∀ i, EqOn (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (fun x => Real.exp (-(α i + t * β i) * x)) (Ioi 0) :=
    fun i x hx => by simp only [abs_of_pos (show (0 : ℝ) < x from hx)]
  have hi : ∀ i, Integrable (fun x : ℝ => Real.exp (-(α i + t * β i) * |x|)) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hp i)) 0).congr_fun (e1 i).symm measurableSet_Ioi
  have hv : ∀ i, ∫ x in Ioi (0 : ℝ), Real.exp (-(α i + t * β i) * |x|) = (α i + t * β i)⁻¹ := fun i => by
    rw [setIntegral_congr_fun measurableSet_Ioi (e1 i), integral_exp_mul_Ioi (neg_neg_of_pos (hp i))]
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have e2 : ∀ y : I → ℝ, ((fun y : I → ℝ => ENNReal.ofReal (c * ∏ i, Real.exp (-α i * |y i|))) *
      fun y : I → ℝ => ENNReal.ofReal ((∏ i, Real.exp (-β i * |y i|)) ^ t)) y =
      ENNReal.ofReal (c * ∏ i, Real.exp (-(α i + t * β i) * |y i|)) := fun y => by
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [lintegral_congr e2, ← ofReal_integral_eq_lintegral_ofReal ((Integrable.fintype_prod hi).const_mul c)
    (.of_forall fun y => by positivity), integral_const_mul,
    integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => Real.exp (-(α i + t * β i) * |x|))]
  simp only [hv, Finset.prod_inv_distrib, div_eq_mul_inv]
end CompanionTheory.RgFd
