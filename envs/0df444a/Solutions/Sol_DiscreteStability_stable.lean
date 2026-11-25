-- Prove2me | solution 1 for DiscreteStability.stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:52.698668+00:00
-- url     : https://prove2.me/submissions/026db426-eeff-477f-8937-cafed4a90a04

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
import Theorems.Thm_DiscreteStability_trap

set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]
namespace DiscreteStability
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2) (hH1 : IsolatedMax f xbar) :
    UniformlyStable P g xbar := by
  intro ε hε
  obtain ⟨ρ, hρ, hρε, -, -, δ, hδ, htrap⟩ := trap hH hP hΛ hS1 hH1 hε
  exact ⟨δ, hδ, fun k₀ x hx hx0 k hk => ((htrap k₀ x hx hx0 k hk).1).trans_le hρε⟩
end DiscreteStability
