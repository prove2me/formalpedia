-- Prove2me | solution 1 for ConsistentSubmodular.FiniteLaw.expect_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:32.776048+00:00
-- url     : https://prove2.me/submissions/f121ca7a-ee90-4df8-87a5-325e0c85676c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProbability

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem solution {β : Type*} [Fintype β] (F : Ω → β) (v : β → ℝ) :
    μ.expect (fun ω => v (F ω)) =
      ∑ b, μ.probability (fun ω => F ω = b) * v b := by
  classical
  unfold expect probability
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (F ω)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

end
