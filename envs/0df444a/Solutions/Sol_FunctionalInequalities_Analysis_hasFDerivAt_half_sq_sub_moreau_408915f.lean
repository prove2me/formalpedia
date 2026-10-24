-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:00:44.904611+00:00
-- url     : https://prove2.me/submissions/8458f153-0226-4e42-ae43-08aaa8258c2a

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
/-- **The resolvent of a convex function is a gradient** (weak Letwin route, Alexandrov's theorem): if `P z` is a point at which `z − P z` is a subgradient of the convex `f` (the proximal map), then
`w ↦ ½‖w‖² − (f (P w) + ½‖P w − w‖²)` (½‖·‖² minus the Moreau envelope) has derivative `⟪P z, ·⟫` at every `z`. -/
theorem solution
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
    HasFDerivAt (fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2))
      (innerSL ℝ (P z)) z := by
  let g : E → ℝ := fun w =>
    (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2)
  have hbound (w : E) :
      0 ≤ g w - g z - ⟪P z, w - z⟫ ∧
        g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2) * ‖w - z‖ ^ 2 := by
    have hpw := hP w (P z)
    have hpz := hP z (P w)
    have hsq := sq_nonneg ‖(w - z) - (P w - P z)‖
    have hsq' := sq_nonneg ‖P w - P z‖
    dsimp only [g]
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
      at hpw hpz hsq hsq' ⊢
    simp only [real_inner_comm] at hpw hpz hsq hsq' ⊢
    constructor
    · linarith only [hpw, hsq']
    · linarith only [hpz, hsq]
  change HasFDerivAt g (innerSL ℝ (P z)) z
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hn : ContinuousAt (fun w : E => ‖w - z‖) z :=
    (continuousAt_id.sub continuousAt_const).norm
  have he : ∀ᶠ w in 𝓝 z, ‖w - z‖ < c :=
    hn.eventually_lt continuousAt_const (by simpa only [sub_self, norm_zero] using hc)
  filter_upwards [he] with w hw
  change ‖g w - g z - ⟪P z, w - z⟫‖ ≤ c * ‖w - z‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound w).1]
  calc
    g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2) * ‖w - z‖ ^ 2 := (hbound w).2
    _ ≤ c * ‖w - z‖ := by
      have hm := mul_le_mul_of_nonneg_right hw.le (norm_nonneg (w - z))
      nlinarith only [hm, sq_nonneg ‖w - z‖]
