-- Prove2me | solution 1 for FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:53.795403+00:00
-- url     : https://prove2.me/submissions/c197da15-a4f7-4fca-84d1-2a5c68732b6e

import Definitions.Def_KLSModular_FunctionalInequalities_L2_Components

noncomputable section
open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory
variable {α : Type*} [MeasurableSpace α]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
section InnerProduct
variable {F : Type*}
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
private theorem FunctionalInequalities.L2.norm_sq_eq_integral_norm_sq {μ : Measure α} (f : Lp F 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
private theorem FunctionalInequalities.L2.integrable_norm_sq
    {μ : Measure α} (f : Lp F 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f
end InnerProduct
/-- Parseval in `L²(μ; G)`: the squared norms of the components in an orthonormal basis add up
to the squared norm. -/
theorem solution {μ : Measure α} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 μ) :
    ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 = ‖g‖ ^ 2 := by
  rw [FunctionalInequalities.L2.norm_sq_eq_integral_norm_sq g]
  rw [Finset.sum_congr rfl (fun k _ => FunctionalInequalities.L2.norm_sq_eq_integral_norm_sq ((innerSL ℝ (b k)).compLp g))]
  rw [← integral_finsetSum _ (fun k _ => FunctionalInequalities.L2.integrable_norm_sq _)]
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂μ, ∀ k, ((innerSL ℝ (b k)).compLp g) x = ⟪b k, g x⟫ := by
    rw [ae_all_iff]
    intro k
    filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ (b k)) g] with x hx
    rw [hx, innerSL_apply_apply]
  filter_upwards [hae] with x hx
  simp only [hx]
  simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right (g x)
