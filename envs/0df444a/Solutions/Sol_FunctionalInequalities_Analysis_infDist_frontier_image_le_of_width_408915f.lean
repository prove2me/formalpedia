-- Prove2me | solution 1 for FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:09:41.178806+00:00
-- url     : https://prove2.me/submissions/2755e770-418a-4524-bbb4-e72d584342bf

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_infDist_frontier_le_of_forall_inner_le_408915f

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Width ratios control the distance to the frontier after an affine normalisation** (weak Letwin
route, Caffarelli's argument): if a bounded open `S ∋ x` has width at most `α` above `x` and
at least `β > 0` below `x` in the unit direction `θ`, and `e` is an affine equivalence with
`e '' S ⊆ closedBall 0 C₀`, then `infDist (e x) (frontier (e '' S)) ≤ 2 C₀ α / β`. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hup : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ α) (hlow : ∃ y ∈ S, ⟪y - x, θ⟫ ≤ -β)
    (e : E ≃ᵃ[ℝ] E) {C₀ : ℝ} (hC₀ : 0 < C₀) (himg : e '' S ⊆ closedBall (0 : E) C₀) :
    infDist (e x) (frontier (e '' S)) ≤ 2 * C₀ * α / β := by
  have _ := hb
  have _ := hθ
  have _ := hC₀
  let η : E := LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) θ
  obtain ⟨y₀, hy₀, hlow₀⟩ := hlow
  have hinner (y : E) : ⟪e y - e x, η⟫ = ⟪y - x, θ⟫ := by
    dsimp only [η]
    have hmap : e y - e x = e.linear (y - x) := by
      have hm := e.toAffineMap.linearMap_vsub y x
      change e.linear (y - x) = e y - e x at hm
      exact hm.symm
    calc
      ⟪e y - e x, LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) θ⟫ =
          ⟪e.linear (y - x),
            LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) θ⟫ := by
        rw [hmap]
      _ = ⟪(e.linear.symm : E →ₗ[ℝ] E) (e.linear (y - x)), θ⟫ :=
        LinearMap.adjoint_inner_right (e.linear.symm : E →ₗ[ℝ] E)
          (e.linear (y - x)) θ
      _ = ⟪y - x, θ⟫ := by
        change ⟪e.linear.symm (e.linear (y - x)), θ⟫ = ⟪y - x, θ⟫
        exact congrArg (fun w : E => ⟪w, θ⟫) (e.linear.symm_apply_apply (y - x))
  have hη : η ≠ 0 := by
    intro hzero
    have hz := hinner (x + θ)
    rw [hzero] at hz
    have hz' : ⟪θ, θ⟫ = 0 := by
      simpa only [inner_zero_right, add_sub_cancel_left] using hz.symm
    have hone : ⟪θ, θ⟫ = 1 := by
      calc
        ⟪θ, θ⟫ = ‖θ‖ ^ 2 := real_inner_self_eq_norm_sq θ
        _ = 1 := by rw [hθ]; norm_num
    linarith
  have hnormη : 0 < ‖η‖ := norm_pos_iff.mpr hη
  let θ' : E := ‖η‖⁻¹ • η
  have hθ' : ‖θ'‖ = 1 := by
    dsimp only [θ']
    calc
      ‖‖η‖⁻¹ • η‖ = ‖‖η‖⁻¹‖ * ‖η‖ := norm_smul _ _
      _ = ‖η‖⁻¹ * ‖η‖ := by
        rw [norm_inv, Real.norm_eq_abs, abs_of_pos hnormη]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hnormη)
  have hS' : IsOpen (e '' S) := by
    change IsOpen ((AffineEquiv.toContinuousAffineEquiv e).toHomeomorph '' S)
    exact (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph.isOpenMap S hS
  have hb' : Bornology.IsBounded (e '' S) :=
    (Metric.isBounded_closedBall : Bornology.IsBounded (closedBall (0 : E) C₀)).subset himg
  have hx' : e x ∈ e '' S := ⟨x, hx, rfl⟩
  have himage : ∀ z ∈ e '' S, ⟪z - e x, θ'⟫ ≤ α / ‖η‖ := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    dsimp only [θ']
    calc
      ⟪e y - e x, ‖η‖⁻¹ • η⟫ =
          ‖η‖⁻¹ * ⟪e y - e x, η⟫ := by
        rw [real_inner_smul_right]
      _ = ‖η‖⁻¹ * ⟪y - x, θ⟫ := by
        rw [hinner y]
      _ ≤ ‖η‖⁻¹ * α :=
        mul_le_mul_of_nonneg_left (hup y hy) (inv_nonneg.mpr (le_of_lt hnormη))
      _ = α / ‖η‖ := by
        rw [div_eq_mul_inv]
        ring
  have hfront :
      infDist (e x) (frontier (e '' S)) ≤ α / ‖η‖ :=
    FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le_408915f hS' hb' hx' hθ' himage
  have hey : ‖e y₀‖ ≤ C₀ := by
    simpa only [mem_closedBall, dist_zero_right] using
      himg ⟨y₀, hy₀, rfl⟩
  have hex : ‖e x‖ ≤ C₀ := by
    simpa only [mem_closedBall, dist_zero_right] using
      himg ⟨x, hx, rfl⟩
  have hdiff : ‖e y₀ - e x‖ ≤ 2 * C₀ := by
    calc
      ‖e y₀ - e x‖ ≤ ‖e y₀‖ + ‖e x‖ := norm_sub_le _ _
      _ ≤ C₀ + C₀ := add_le_add hey hex
      _ ≤ 2 * C₀ := by nlinarith [hC₀]
  have habs₀ : β ≤ |⟪y₀ - x, θ⟫| := by
    have hnonpos : ⟪y₀ - x, θ⟫ ≤ 0 :=
      hlow₀.trans (neg_nonpos.mpr hβ.le)
    rw [abs_of_nonpos hnonpos]
    linarith
  have habs : β ≤ |⟪e y₀ - e x, η⟫| := by
    rw [hinner y₀]
    exact habs₀
  have hβnorm : β ≤ 2 * C₀ * ‖η‖ := by
    calc
      β ≤ |⟪e y₀ - e x, η⟫| := habs
      _ ≤ ‖e y₀ - e x‖ * ‖η‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * C₀) * ‖η‖ :=
        mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      _ = 2 * C₀ * ‖η‖ := by ring
  have hratio : α / ‖η‖ ≤ 2 * C₀ * α / β := by
    apply (div_le_iff₀ hnormη).2
    calc
      α ≤ (2 * C₀ * α) * ‖η‖ / β := by
        apply (le_div_iff₀ hβ).2
        calc
          α * β ≤ α * (2 * C₀ * ‖η‖) :=
            mul_le_mul_of_nonneg_left hβnorm hα
          _ = (2 * C₀ * α) * ‖η‖ := by ring
      _ = (2 * C₀ * α / β) * ‖η‖ := by ring
  exact hfront.trans hratio
