-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:01:39.714049+00:00
-- url     : https://prove2.me/submissions/59c2ed22-758d-477e-bc03-24f22c30511d

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_half_sq_sub_moreau_408915f

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12D3MoreauSymmetricDerivative
open Set Filter
open scoped RealInnerProductSpace Topology
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
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **The derivative of the resolvent is symmetric and firmly nonexpansive**: at a point
where the proximal map `P` is differentiable with derivative `T`, `⟪T v, w⟫ = ⟪v, T w⟫` and
`‖T v‖² ≤ ⟪T v, v⟫`. -/
theorem solution
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E}
    {T : E →L[ℝ] E} (hT : HasFDerivAt P T z) (v w : E) :
    ⟪T v, w⟫ = ⟪v, T w⟫ ∧ ‖T v‖ ^ 2 ≤ ⟪T v, v⟫ := by
  constructor
  · have hs := second_derivative_symmetric
      (fun y => FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_408915f hP y)
      ((innerSL ℝ : E →L[ℝ] (E →L[ℝ] ℝ)).hasFDerivAt.comp z hT) v w
    change ⟪T v, w⟫ = ⟪T w, v⟫ at hs
    exact hs.trans (real_inner_comm (T w) v).symm
  · have hfirm (a b : E) :
        ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫ := by
      have hab := hP a (P b)
      have hba := hP b (P a)
      simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
        at hab hba ⊢
      simp only [real_inner_comm] at hab hba ⊢
      linarith only [hab, hba]
    have hline : HasDerivAt (fun t : ℝ => P (z + t • v)) (T v) 0 := by
      have hp : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
        simpa only [id_eq, one_smul] using
          ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
      have ht : HasFDerivAt P T (z + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using hT
      exact ht.comp_hasDerivAt 0 hp
    have hlim :
        Tendsto (fun t : ℝ => t⁻¹ • (P (z + t • v) - P z))
          (𝓝[≠] 0) (𝓝 (T v)) := by
      simpa only [zero_add, zero_smul, add_zero] using hline.tendsto_slope_zero
    have hquot (t : ℝ) :
        ‖t⁻¹ • (P (z + t • v) - P z)‖ ^ 2 ≤
          ⟪t⁻¹ • (P (z + t • v) - P z), v⟫ := by
      by_cases ht : t = 0
      · simp [ht]
      · have hp := hfirm (z + t • v) z
        simp only [add_sub_cancel_left, real_inner_smul_right] at hp
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_left]
        calc
          (t⁻¹) ^ 2 * ‖P (z + t • v) - P z‖ ^ 2 ≤
              (t⁻¹) ^ 2 * (t * ⟪P (z + t • v) - P z, v⟫) :=
            mul_le_mul_of_nonneg_left hp (sq_nonneg t⁻¹)
          _ = t⁻¹ * ⟪P (z + t • v) - P z, v⟫ := by
            field_simp [ht]
    exact le_of_tendsto_of_tendsto (hlim.norm.pow 2)
      (hlim.inner tendsto_const_nhds) (Filter.Eventually.of_forall hquot)
