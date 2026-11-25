-- Prove2me | solution 1 for DiscreteStability.exists_pos_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:33:04.750951+00:00
-- url     : https://prove2.me/submissions/66976a9e-2e3f-45e9-af5d-2659bbc01d5a

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_DiscreteStability_Basic

set_option autoImplicit true
open scoped RealInnerProductSpace
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace DiscreteStability
theorem _root_.solution {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {φ : X → ℝ} (hc : ContinuousOn φ K) (hpos : ∀ x ∈ K, 0 < φ x) :
    ∃ m > 0, ∀ x ∈ K, m ≤ φ x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn h hc
    exact ⟨φ x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩
end DiscreteStability
