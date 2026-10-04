-- Prove2me | solution 1 for Disjunctive.CutCorrespondence.cglpk_basicness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:27:45.034825+00:00
-- url     : https://prove2.me/submissions/d5cd853a-6d4b-4fa5-aada-af88ddb46890

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp

set_option autoImplicit false

open Disjunctive.CutCorrespondence in
theorem solution {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β)
    (hnd : ¬ IsDominatedByLP Atil btil α β) : 0 < u0 ∧ 0 < v0 := by
  have hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β := hbasic.1
  obtain ⟨h1, h2, h3, h4, _, hu, hv, hu0, hv0⟩ := hf
  constructor
  · by_contra hc
    have e : u0 = 0 := le_antisymm (not_lt.mp hc) hu0
    apply hnd
    refine ⟨u, hu, fun i => ?_, ?_⟩
    · have := h1 i
      rw [e] at this
      simp only [ite_self, add_zero] at this
      linarith
    · linarith
  · by_contra hc
    have e : v0 = 0 := le_antisymm (not_lt.mp hc) hv0
    apply hnd
    refine ⟨v, hv, fun i => ?_, ?_⟩
    · have := h2 i
      rw [e] at this
      simp only [ite_self, sub_zero] at this
      linarith
    · rw [e] at h4
      linarith
