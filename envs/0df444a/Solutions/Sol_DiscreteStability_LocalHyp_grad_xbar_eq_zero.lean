-- Prove2me | solution 1 for DiscreteStability.LocalHyp.grad_xbar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:44:13.623597+00:00
-- url     : https://prove2.me/submissions/d90c22c0-9ab1-4bfa-a214-2647f2896d47

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability

set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
namespace DiscreteStability
namespace LocalHyp
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L) (hH1 : IsolatedMax f xbar) :
    g xbar = 0 := by
  obtain ⟨r, hr, hmax⟩ := hH1
  have hloc : IsLocalMax f xbar := by
    filter_upwards [Metric.ball_mem_nhds xbar hr] with y hy
    by_cases hyx : y = xbar
    · rw [hyx]
    · exact (hmax y hyx (le_of_lt (mem_ball.mp hy))).le
  have h0 := hloc.hasFDerivAt_eq_zero (hH.grad xbar (mem_closedBall_self hH.r₀_pos.le))
  have : ⟪g xbar, g xbar⟫ = 0 := by
    have := congrArg (fun φ => φ (g xbar)) h0
    simpa [innerSL_apply_apply] using this
  exact inner_self_eq_zero.mp this
end LocalHyp
end DiscreteStability
