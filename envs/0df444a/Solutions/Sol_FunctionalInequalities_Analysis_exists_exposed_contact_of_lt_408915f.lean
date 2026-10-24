-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_exposed_contact_of_lt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:09:42.29385+00:00
-- url     : https://prove2.me/submissions/e6543b41-ce3d-48b7-a2ad-1dd15608bc24

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

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F1StrictConvexityElementary
open Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **A strictly exposed contact point below a level** (weak Letwin route; KLS500
`exists_strict_exposed_contact_in_sublevel`): if `{u ≤ R}` is compact and `u x < R`, the contact set of a
supporting affine function at `x` has a point `z` with `u z < R` that is strictly exposed in the direction
`θ` among the contact points with `u ≤ R`. -/
theorem solution {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {R : ℝ} (hR : u x < R) (hK : IsCompact {y | u y ≤ R}) :
    ∃ z θ : E, u z = u x + ⟪p, z - x⟫ ∧ u z < R ∧
      ∀ y, u y = u x + ⟪p, y - x⟫ → u y ≤ R → y ≠ z → ⟪y - z, θ⟫ < 0 := by
  have hu : Continuous u := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  let C : Set E := {y | u y = u x + ⟪p, y - x⟫} ∩ {y | u y ≤ R}
  have hclosed : IsClosed {y | u y = u x + ⟪p, y - x⟫} :=
    isClosed_eq hu (continuous_const.add
      (continuous_const.inner (continuous_id.sub continuous_const)))
  have hC : IsCompact C := hK.inter_left hclosed
  have hxC : x ∈ C := by
    refine ⟨?_, hR.le⟩
    change u x = u x + ⟪p, x - x⟫
    exact le_antisymm (by simp) (hp x)
  obtain ⟨M, hM, hbound⟩ := hC.isBounded.exists_pos_norm_le
  let ε : ℝ := (R - u x) / (2 * (M ^ 2 + 1))
  have hden : 0 < 2 * (M ^ 2 + 1) := by positivity
  have hε : 0 < ε := div_pos (sub_pos.mpr hR) hden
  have hεeq : ε * (2 * (M ^ 2 + 1)) = R - u x :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hεM : ε * M ^ 2 < R - u x := by
    nlinarith [mul_nonneg hε.le (sq_nonneg M)]
  let F : E → ℝ := fun y => ε * ‖y‖ ^ 2 - ⟪p, y⟫
  have hF : Continuous F :=
    (continuous_const.mul (continuous_norm.pow 2)).sub
      (continuous_const.inner continuous_id)
  obtain ⟨z, hzC, hzmax⟩ := hC.exists_isMaxOn ⟨x, hxC⟩ hF.continuousOn
  have hmax : ∀ y ∈ C, F y ≤ F z := isMaxOn_iff.mp hzmax
  have hzcontact : u z = u x + ⟪p, z - x⟫ := hzC.1
  have hzsq : ‖z‖ ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) hM.le).mpr (hbound z hzC)
  have hzquad : ε * ‖z‖ ^ 2 ≤ ε * M ^ 2 := mul_le_mul_of_nonneg_left hzsq hε.le
  have hxquad : 0 ≤ ε * ‖x‖ ^ 2 := mul_nonneg hε.le (sq_nonneg ‖x‖)
  have hzR : u z < R := by
    have hxmax := hmax x hxC
    dsimp [F] at hxmax
    have hzcontact' := hzcontact
    rw [inner_sub_right] at hzcontact'
    linarith
  let θ : E := (2 * ε) • z - p
  refine ⟨z, θ, hzcontact, hzR, ?_⟩
  intro y hy hyR hyz
  have hymax := hmax y ⟨hy, hyR⟩
  have hnorm : 0 < ‖y - z‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz))
  have hpos : 0 < ε * ‖y - z‖ ^ 2 := mul_pos hε hnorm
  have hid : ⟪y - z, θ⟫ = F y - F z - ε * ‖y - z‖ ^ 2 := by
    rw [real_inner_comm θ (y - z)]
    dsimp [θ, F]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_sub_sq_real]
    rw [real_inner_comm z y]
    ring
  rw [hid]
  linarith
