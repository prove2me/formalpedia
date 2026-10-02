-- Prove2me | solution 1 for Disjunctive.ConvexHull.tightness_lifted_representation
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:52:43.26623+00:00
-- url     : https://prove2.me/submissions/f08cdf36-869b-4243-adc5-010eb4bf4107

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Cex9adb667b
open Disjunctive.ConvexHull

/-- The single disjunct `0 * x ≥ 1` in `ℝ¹`: its polyhedron is empty, its recession cone is all of `ℝ¹`. -/
noncomputable def mm : Unit → ℕ := fun _ => 1
noncomputable def AA : (h : Unit) → Matrix (Fin (mm h)) (Fin 1) ℝ := fun _ => fun _ _ => 0
noncomputable def bb : (h : Unit) → Fin (mm h) → ℝ := fun _ => fun _ => 1

theorem feas_empty : FeasibleIndices mm AA bb = ∅ := by
  ext h
  simp only [FeasibleIndices, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx⟩
  have h0 := hx ⟨0, by simp [mm]⟩
  simp [AA, bb, Matrix.mulVec, dotProduct] at h0
  linarith

theorem proj_univ_empty : ProjX (LiftedPolyhedron mm AA bb Set.univ) = ∅ := by
  ext x
  simp only [ProjX, LiftedPolyhedron, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨y, y0⟩, -, hA, -, hs⟩
  have h1 := (hA () (Set.mem_univ _)).1 ⟨0, by simp [mm]⟩
  simp [AA, bb, Matrix.mulVec, dotProduct] at h1 hs
  linarith

theorem proj_feas_empty : ProjX (LiftedPolyhedron mm AA bb (FeasibleIndices mm AA bb)) = ∅ := by
  rw [feas_empty]
  ext x
  simp only [ProjX, LiftedPolyhedron, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨y, y0⟩, -, -, hz, hs⟩
  have h1 := (hz () not_false).2
  simp at hs h1
  rw [h1] at hs
  norm_num at hs

theorem rhs_false : ¬ (∀ k, k ∉ FeasibleIndices mm AA bb →
    RecessionCone (AA k) ⊆ MinkowskiSumOver (FeasibleIndices mm AA bb) (fun h => RecessionCone (AA h))) := by
  intro h
  have hk : () ∉ FeasibleIndices mm AA bb := by rw [feas_empty]; exact Set.notMem_empty _
  have hmem : (fun _ => (1 : ℝ)) ∈ RecessionCone (AA ()) := by
    simp only [RecessionCone, Set.mem_setOf_eq]
    intro i
    simp [AA, Matrix.mulVec, dotProduct]
  obtain ⟨y, hy, -, hz⟩ := h () hk hmem
  rw [feas_empty] at hz
  have := hz () (Set.notMem_empty _)
  have h1 := congrFun hy 0
  simp [this] at h1

theorem cex : ¬ (∀ {n : ℕ} {Q : Type} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ),
    ProjX (LiftedPolyhedron m A b Set.univ) = ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) ↔
      ∀ k, k ∉ FeasibleIndices m A b →
        RecessionCone (A k) ⊆ MinkowskiSumOver (FeasibleIndices m A b) (fun h => RecessionCone (A h))) := by
  intro h
  exact rhs_false ((h mm AA bb).1 (by rw [proj_univ_empty, proj_feas_empty]))

end Cex9adb667b

open Disjunctive.ConvexHull in
theorem solution : ¬ (∀ {n : ℕ} {Q : Type} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ),
    ProjX (LiftedPolyhedron m A b Set.univ) = ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) ↔
      ∀ k, k ∉ FeasibleIndices m A b →
        RecessionCone (A k) ⊆ MinkowskiSumOver (FeasibleIndices m A b) (fun h => RecessionCone (A h))) := by
  exact Cex9adb667b.cex

