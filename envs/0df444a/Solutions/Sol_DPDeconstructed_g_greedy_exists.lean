-- Prove2me | solution 1 for DPDeconstructed.g_greedy_exists
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:20:15.002433+00:00
-- url     : https://prove2.me/submissions/5ac0b3a7-ae3a-42bd-99b2-717032f10ec7

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

open DPDeconstructed DPDeconstructed.DynProg DPDeconstructed.PlanFactorization in
theorem solution {X A : Type*} [Nonempty X] (D : DynProg X A) (𝕍 : Set (X → ℝ))
    (h21 : D.Assumption21 𝕍) (P : PlanFactorization D) :
    ∀ g ∈ P.bbG 𝕍, ∃ σ : D.Policy, P.IsGGreedy g σ := by
  rintro g ⟨v, hv, rfl⟩
  obtain ⟨σ, hσ⟩ := h21.2.2 v hv
  have hv' : v ∈ D.𝒱 := h21.1 hv
  refine ⟨σ, fun x => ?_⟩
  unfold DynProg.Mσ DynProg.M
  simp_rw [P.factor v hv']
  simpa only [DynProg.Tσ, DynProg.T] using hσ x
