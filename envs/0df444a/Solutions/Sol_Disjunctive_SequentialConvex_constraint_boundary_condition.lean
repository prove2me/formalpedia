-- Prove2me | solution 1 for Disjunctive.SequentialConvex.constraint_boundary_condition
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:25:43.759789+00:00
-- url     : https://prove2.me/submissions/1b9850d4-8dcc-4782-b927-b95a03ac9415

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

open Disjunctive.SequentialConvex

theorem solution : ¬ (∀ {n : ℕ} (Fjm1 : Set (Fin n → ℝ)) {Qj : Type} [Fintype Qj]
    (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ),
    (convexHull ℝ (convexHull ℝ Fjm1 ∩ Dj d d0) = convexHull ℝ (Fjm1 ∩ Dj d d0)) ↔
      (∀ x ∈ Fjm1 ∩ Dbarj d d0, ∀ y ∈ Fjm1 ∩ Dj d d0,
        segment ℝ x y ∩ intrinsicFrontier ℝ (Dbarj d d0) ⊆ convexHull ℝ (Fjm1 ∩ Dj d d0))) := by
  intro h
  let c : ℝ → (Fin 1 → ℝ) := fun t _ => t
  set F : Set (Fin 1 → ℝ) := {c (-1), c (1 / 2)} with hF
  set d : Fin 2 → Fin 1 → ℝ := fun _ _ => 1 with hd
  set d0 : Fin 2 → ℝ := ![0, 1] with hd0
  have hdot : ∀ (i : Fin 2) (z : Fin 1 → ℝ), dotProduct (d i) z = z 0 := by
    intro i z; simp [hd, dotProduct]
  have hD : ∀ z, z ∈ Dj d d0 ↔ 0 ≤ z 0 := by
    intro z
    simp only [Dj, HalfspaceGE, Set.mem_iUnion, Set.mem_setOf_eq, hdot]
    constructor
    · rintro ⟨i, hi⟩; fin_cases i <;> simp [hd0] at hi <;> linarith
    · intro hz; exact ⟨0, by simpa [hd0] using hz⟩
  have hDbar : ∀ z, z ∈ Dbarj d d0 ↔ z 0 ≤ 1 := by
    intro z
    simp only [Dbarj, HalfspaceLE, Set.mem_iUnion, Set.mem_setOf_eq, hdot]
    constructor
    · rintro ⟨i, hi⟩; fin_cases i <;> simp [hd0] at hi <;> linarith
    · intro hz; exact ⟨1, by simpa [hd0] using hz⟩
  have hFD : F ∩ Dj d d0 = {c (1 / 2)} := by
    ext z
    simp only [Set.mem_inter_iff, hF, Set.mem_insert_iff, Set.mem_singleton_iff, hD]
    constructor
    · rintro ⟨rfl | rfl, hz⟩
      · simp [c] at hz; linarith
      · rfl
    · rintro rfl; exact ⟨Or.inr rfl, by simp [c]⟩
  -- the right-hand side holds: the frontier of `D̄ = {z₀ ≤ 1}` is far away
  have hrhs : ∀ x ∈ F ∩ Dbarj d d0, ∀ y ∈ F ∩ Dj d d0,
      segment ℝ x y ∩ intrinsicFrontier ℝ (Dbarj d d0) ⊆ convexHull ℝ (F ∩ Dj d d0) := by
    rintro x ⟨hxF, -⟩ y hy z ⟨hz, hzf⟩
    exfalso
    rw [hFD] at hy
    have hy' : y = c (1 / 2) := hy
    have hz0 : z 0 ≤ 1 / 2 := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      have hx0 : x 0 ≤ 1 / 2 := by
        rcases hxF with rfl | rfl <;> simp [c] <;> norm_num
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy', c]
      nlinarith
    have hint : z ∈ interior (Dbarj d d0) := by
      have hopen : IsOpen {w : Fin 1 → ℝ | w 0 < 1} :=
        isOpen_lt (continuous_apply 0) continuous_const
      refine interior_maximal (fun w hw => (hDbar w).mpr (le_of_lt hw)) hopen ?_
      show z 0 < 1
      linarith
    have := intrinsicFrontier_subset_frontier hzf
    exact this.2 hint
  have hlhs := (h F d d0).mpr hrhs
  -- but `0 ∈ conv(conv F ∩ D)` while `conv(F ∩ D) = {c (1/2)}`
  have h0 : (0 : Fin 1 → ℝ) ∈ convexHull ℝ (convexHull ℝ F ∩ Dj d d0) := by
    apply subset_convexHull
    refine ⟨?_, (hD 0).mpr (by simp)⟩
    apply segment_subset_convexHull (show c (-1) ∈ F by simp [hF]) (show c (1/2) ∈ F by simp [hF])
    refine ⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i; simp [c]; norm_num
  rw [hlhs, hFD, convexHull_singleton] at h0
  have := congrFun h0 0
  simp [c] at this

#print axioms solution
