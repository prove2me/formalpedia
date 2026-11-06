-- Prove2me | solution 1 for BianchiIX.eventually_no_intermediate_return
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:45:59.195505+00:00
-- url     : https://prove2.me/submissions/8068e7c4-8a72-4619-a704-662a2dd37e39

import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X]


/-- Local uniqueness at both crossings and compact interior avoidance persist. -/
theorem solution {x₀ : X} {T : X → ℝ}
    {g : X → ℝ → ℝ} {c : ℝ} (hT : ContinuousAt T x₀) (hpos : 0 < T x₀)
    (hentry : ∀ᶠ z : X × ℝ in 𝓝 (x₀, 0), g z.1 z.2 = c → z.2 = 0)
    (hexit : ∀ᶠ z : X × ℝ in 𝓝 (x₀, T x₀), g z.1 z.2 = c → z.2 = T z.1)
    (hcont : ∀ t ∈ Ioo 0 (T x₀), ContinuousAt (fun z : X × ℝ => g z.1 z.2) (x₀, t))
    (havoid : ∀ t ∈ Ioo 0 (T x₀), g x₀ t ≠ c) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Ioo 0 (T x), g x t ≠ c := by
  have H : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc 0 (T x), g x t = c → t = 0 ∨ t = T x := by
    apply eventually_forall_movingInterval hT hpos
    intro t ht
    by_cases hzero : t = 0
    · subst t
      exact hentry.mono fun _ h heq => Or.inl (h heq)
    by_cases hend : t = T x₀
    · subst t
      exact hexit.mono fun _ h heq => Or.inr (h heq)
    have hi : t ∈ Ioo 0 (T x₀) :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hend⟩
    exact ((hcont t hi).eventually_ne (havoid t hi)).mono fun _ h heq => (h heq).elim
  filter_upwards [H] with x hx
  intro t ht heq
  rcases hx t ⟨ht.1.le, ht.2.le⟩ heq with h | h
  · exact (ne_of_gt ht.1) h
  · exact (ne_of_lt ht.2) h
