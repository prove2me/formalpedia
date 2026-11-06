-- Prove2me | solution 1 for BianchiIX.contDiffAt_scalar_event_branch
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:06:22.604943+00:00
-- url     : https://prove2.me/submissions/c1555f22-da7d-44ed-bf8c-a7c83c51e0b0

import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology


/-- A continuous transverse branch inherits the regularity of its defining equation. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    {n : WithTop ℕ∞} (hn : n ≠ 0) (hQ : ContDiffAt ℝ n Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0)
    {τ : E → ℝ} (hτ : τ x = t) (hcτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) : ContDiffAt ℝ n τ x := by
  have htime : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      a • ContinuousLinearMap.id ℝ ℝ := by
    have H := ((hQ.differentiableAt hn).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right x t)).unique hd.hasFDerivAt
    rw [H]
    ext
    simp [mul_comm]
  have hinv : ((fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [htime]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := a⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [ha]
    · ext
      simp [ha]
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    simpa only [hτ, id_eq] using (continuousAt_id.prodMk hcτ).tendsto
  have heq : τ =ᶠ[𝓝 x] hQ.implicitFunction hn hinv := by
    filter_upwards [hhit,
      hgraph.eventually (hQ.eventually_apply_eq_iff_implicitFunction hn hinv)] with y hy hiff
    exact (hiff.mp hy).symm
  exact (hQ.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq heq
