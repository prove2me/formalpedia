-- Prove2me | solution 1 for AvramDividend.Classical.continuous_argmin_sInf_zero_or_minimal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:53:04.242097+00:00
-- url     : https://prove2.me/submissions/fa8f78ff-39c4-4bb8-a8f3-067044c60890

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false
open Set

theorem solution (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ioi 0))
    (hne : {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x}.Nonempty) :
    sInf {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x} = 0 ∨
      (0 < sInf {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x} ∧
        ∀ x : ℝ, 0 < x →
          f (sInf {a : ℝ | 0 < a ∧ ∀ y : ℝ, 0 < y → f a ≤ f y}) ≤ f x) := by
  let A : Set ℝ := {a : ℝ | 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x}
  have hA : A.Nonempty := hne
  have hb : BddBelow A := ⟨0, fun a ha => ha.1.le⟩
  have h0 : 0 ≤ sInf A := le_csInf hA (fun a ha => ha.1.le)
  change sInf A = 0 ∨ (0 < sInf A ∧ ∀ x : ℝ, 0 < x → f (sInf A) ≤ f x)
  by_cases hz : sInf A = 0
  · exact Or.inl hz
  · have hi : 0 < sInf A := lt_of_le_of_ne h0 (Ne.symm hz)
    refine Or.inr ⟨hi, ?_⟩
    intro x hx
    exact ContinuousWithinAt.closure_le (csInf_mem_closure hA hb)
      ((hcont (sInf A) hi).mono (fun a ha => ha.1)) continuousWithinAt_const
      (fun a ha => ha.2 x hx)
