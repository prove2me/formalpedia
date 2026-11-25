-- Prove2me | solution 1 for DiscreteStability.asympStable_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:27.664017+00:00
-- url     : https://prove2.me/submissions/6309f41b-45ac-4ba6-af72-df1c8c3094aa

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
import Theorems.Thm_DiscreteStability_LocalHyp_continuousOn
import Theorems.Thm_DiscreteStability_LocalHyp_continuousOn_grad
import Theorems.Thm_DiscreteStability_trap
import Theorems.Thm_DiscreteStability_stable
import Theorems.Thm_DiscreteStability_tendsto_of_weighted_ascent

set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]
namespace DiscreteStability
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L)
    (hP : ∀ k, StepBound (P k) (lo k) (hi k)) (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2)
    (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hW : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k * (2 - L * hi k)) atTop atTop) :
    UniformlyAsympStable P g xbar := by
  refine ⟨stable hH hP hΛ hS1 hH1, ?_⟩
  obtain ⟨r₂, hr₂, hcrit⟩ := hH2
  obtain ⟨ρ, hρ, hρR, hρr₀, hρmax, δ, hδ, htrap⟩ := trap hH hP hΛ hS1 hH1 hr₂
  refine ⟨δ, hδ, fun k₀ x hx hx0 => ?_⟩
  have hL := hH.L_nonneg
  have hLhi : ∀ k, L * hi k ≤ 2 := fun k =>
    (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS1
  refine tendsto_of_weighted_ascent (T := closedBall xbar ρ) (isCompact_closedBall xbar ρ)
    (mem_closedBall_self hρ.le)
    (hH.continuousOn.mono (closedBall_subset_closedBall hρr₀))
    (hH.continuousOn_grad.mono (closedBall_subset_closedBall hρr₀))
    (fun y hy hne => hρmax y hne (mem_closedBall.mp hy))
    (fun y hy hne => hcrit y hne ((mem_closedBall.mp hy).trans hρR))
    (w := fun k => lo k * (2 - L * hi k) / 2)
    (fun k => by have := mul_nonneg (hP k).lo_nonneg (by linarith [hLhi k] : 0 ≤ 2 - L * hi k)
                 positivity)
    ?_ (fun k hk => mem_closedBall.mpr (htrap k₀ x hx hx0 k hk).1.le)
    (fun k hk => (htrap k₀ x hx hx0 k hk).2)
  have : Tendsto (fun N => (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, lo k * (2 - L * hi k))
      atTop atTop := hW.const_mul_atTop (by norm_num)
  refine this.congr fun N => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end DiscreteStability
