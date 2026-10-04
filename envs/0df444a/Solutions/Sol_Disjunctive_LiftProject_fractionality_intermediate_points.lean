-- Prove2me | solution 1 for Disjunctive.LiftProject.fractionality_intermediate_points
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:18:07.27385+00:00
-- url     : https://prove2.me/submissions/e3571f1c-b7e9-484c-b292-09f007447554

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

open Disjunctive.LiftProject

theorem solution : ¬ (∀ {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (i1 ij : Fin n) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Disjunctive.LiftProject.Poly Atil btil) i1) ij,
      β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Disjunctive.LiftProject.Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1),
    0 < xstar ij ∧ xstar ij < 1) := by
  intro h
  set A : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; -1, 0; 0, 1; 0, -1] with hA
  set b : Fin 4 → ℝ := ![0, -1, 2, -2] with hb
  set K : Set (Fin 2 → ℝ) := {x | x 1 = 2 ∧ 0 ≤ x 0 ∧ x 0 ≤ 1} with hK
  have hPK : Disjunctive.LiftProject.Poly A b ⊆ K := by
    intro x hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    simp [hA, hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2 h3
    exact ⟨by linarith, h0, by linarith⟩
  have hKconv : Convex ℝ K := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx0, hx0'⟩ := hx
    obtain ⟨hy1, hy0, hy0'⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx1, hy1]
      linear_combination 2 * hst
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; nlinarith
  have hQK : SplitConvexify (Disjunctive.LiftProject.Poly A b) 0 ⊆ K :=
    convexHull_min (fun x hx => hPK hx.1) hKconv
  have hpt : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ![c, 2] ∈ Disjunctive.LiftProject.Poly A b := by
    intro c hc0 hc1 i
    fin_cases i <;> simp [hA, hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> linarith
  set xs : Fin 2 → ℝ := ![1 / 2, 2] with hxs
  have hxsQ : xs ∈ SplitConvexify (Disjunctive.LiftProject.Poly A b) 0 := by
    have ha : ![(0 : ℝ), 2] ∈ Disjunctive.LiftProject.Poly A b ∩ ZeroOneSet 0 :=
      ⟨hpt 0 le_rfl zero_le_one, Or.inl (by simp)⟩
    have hb' : ![(1 : ℝ), 2] ∈ Disjunctive.LiftProject.Poly A b ∩ ZeroOneSet 0 :=
      ⟨hpt 1 zero_le_one le_rfl, Or.inr (by simp)⟩
    apply segment_subset_convexHull ha hb'
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i
    fin_cases i <;> simp [hxs] <;> norm_num
  have hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Disjunctive.LiftProject.Poly A b) 0) 1,
      (1 / 2 : ℝ) ≤ dotProduct ![1, 0] x := by
    intro x hx
    have hempty : SplitConvexify (Disjunctive.LiftProject.Poly A b) 0 ∩ ZeroOneSet 1 = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hz
      have := (hQK hy).1
      rcases hz with hz | hz <;> rw [hz] at this <;> norm_num at this
    rw [SplitConvexify, hempty, convexHull_empty] at hx
    exact hx.elim
  have hExt : xs ∈ Set.extremePoints ℝ
      (SplitConvexify (Disjunctive.LiftProject.Poly A b) 0 ∩
        {x | (1 / 2 : ℝ) ≤ dotProduct ![1, 0] x}) := by
    refine ⟨⟨hxsQ, by simp [hxs, dotProduct, Fin.sum_univ_two]⟩, ?_⟩
    rintro y ⟨hyQ, hy⟩ z ⟨hzQ, hz⟩ ⟨s, t, hs, ht, hst, hyz⟩
    have hyK := hQK hyQ
    have hzK := hQK hzQ
    simp only [Set.mem_setOf_eq, dotProduct, Fin.sum_univ_two] at hy hz
    simp at hy hz
    have e0 := congrFun hyz 0
    simp [hxs] at e0
    have hy0 : y 0 = 1 / 2 := by nlinarith
    funext i
    fin_cases i
    · simpa [hxs] using hy0
    · simpa [hxs] using hyK.1
  have := h A b 0 1 ![1, 0] (1 / 2) hValid xs hExt (by simp [hxs]; norm_num)
  simp [hxs] at this

#print axioms solution
