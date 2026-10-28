-- Prove2me | solution 1 for Disjunctive.IntroDuality.farkas_lemma_disjunctive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:32:49.433544+00:00
-- url     : https://prove2.me/submissions/30d03436-24ab-4223-b6df-b933584eadc5

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems
import Theorems.Thm_LinearOptimization_farkas_inequality_form

open Matrix

open Disjunctive.IntroDuality

theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (α : Fin n → ℝ) (α0 : ℝ) :
    (∀ x ∈ ⋃ h : Q, Disjunctive.IntroDuality.Poly (A h) (b h), α0 ≤ dotProduct α x) ↔
      ∀ h : Q, (Disjunctive.IntroDuality.Poly (A h) (b h)).Nonempty →
        ∃ u : Fin (m h) → ℝ, 0 ≤ u ∧ Matrix.vecMul u (A h) = α ∧
          α0 ≤ dotProduct u (b h) := by
  have key : ∀ h : Q, ∀ x, x ∈ Disjunctive.IntroDuality.Poly (A h) (b h) ↔ (-A h).mulVec x ≤ -b h := by
    intro h x
    simp only [Disjunctive.IntroDuality.Poly, Set.mem_setOf_eq, Pi.le_def, Matrix.neg_mulVec, Pi.neg_apply, neg_le_neg_iff]
  constructor
  · intro hall h ⟨x0, hx0⟩
    have hf := (LinearOptimization.farkas_inequality_form (-A h) (-b h) (-α) (-α0)
      ⟨x0, (key h x0).1 hx0⟩).1 (by
        intro x hx
        have := hall x (Set.mem_iUnion.2 ⟨h, (key h x).2 hx⟩)
        simp only [neg_dotProduct]; linarith)
    obtain ⟨p, hp0, hpA, hpb⟩ := hf
    refine ⟨p, hp0, ?_, ?_⟩
    · rw [Matrix.transpose_neg, Matrix.neg_mulVec, neg_inj, Matrix.mulVec_transpose] at hpA
      exact hpA
    · simp only [dotProduct_neg] at hpb; linarith
  · intro hall x hx
    obtain ⟨h, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨u, hu0, huA, hub⟩ := hall h ⟨x, hx⟩
    have : dotProduct u (b h) ≤ dotProduct u ((A h).mulVec x) :=
      dotProduct_le_dotProduct_of_nonneg_left hx hu0
    rw [Matrix.dotProduct_mulVec, huA] at this
    linarith

