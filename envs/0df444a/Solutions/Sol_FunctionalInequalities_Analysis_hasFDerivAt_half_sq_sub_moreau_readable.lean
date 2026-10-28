-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:18.518636+00:00
-- url     : https://prove2.me/submissions/992adcce-4dd5-4a73-ad05-b81753a04b72

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12D3MoreauSymmetricDerivative
open Set Filter
open scoped RealInnerProductSpace Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
