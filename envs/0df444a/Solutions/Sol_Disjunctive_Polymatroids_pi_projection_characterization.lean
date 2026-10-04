-- Prove2me | solution 1 for Disjunctive.Polymatroids.pi_projection_characterization
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:07:28.256579+00:00
-- url     : https://prove2.me/submissions/4ffdfd23-904e-4803-99d5-d203366626e6

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

open Disjunctive.Polymatroids

theorem solution : ¬ (∀ {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ),
    PiSet r1 r2 = PiProjSystem r1 r2) := by
  classical
  intro h
  set r1 : Finset (Fin 1) → ℝ := fun A => if A = ∅ then -1 else 5 with hr1
  set r2 : Finset (Fin 1) → ℝ := fun _ => 1 with hr2
  set π : Fin 1 → ℝ := fun _ => 1 with hπ
  have hmem : π ∈ PiSet r1 r2 := by
    refine ⟨fun _ => by simp [hπ], ?_⟩
    rintro x (hx | hx)
    · exfalso
      have := hx.2 ∅
      simp [SumOver, hr1] at this
      linarith
    · have := hx.2 Finset.univ
      simp only [SumOver, hr2] at this
      simpa [hπ, dotProduct] using this
  rw [h] at hmem
  obtain ⟨u, hu, _, hcov, h1, h2⟩ := hmem
  have hcov0 := hcov 0
  simp only [hπ] at hcov0
  have hsum : ∑ A, u A * r1 A + ∑ A, u A * r2 A = ∑ A, u A * (r1 A + r2 A) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    ring
  have hlow : ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 1) => (0 : Fin 1) ∈ A), u A * 6 ≤
      ∑ A, u A * (r1 A + r2 A) := by
    calc ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 1) => (0 : Fin 1) ∈ A), u A * 6
        = ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 1) => (0 : Fin 1) ∈ A),
            u A * (r1 A + r2 A) := by
          refine Finset.sum_congr rfl fun A hA => ?_
          have hne : A ≠ ∅ := by
            intro h0
            simp [h0] at hA
          simp [hr1, hr2, hne]
          norm_num
      _ ≤ ∑ A, u A * (r1 A + r2 A) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro A _ _
          apply mul_nonneg (hu A)
          by_cases hA : A = ∅ <;> simp [hr1, hr2, hA] <;> norm_num
  rw [← Finset.sum_mul] at hlow
  linarith

#print axioms solution
