-- Prove2me | solution 1 for DantzigSimplex.Technique.theorem_3_no_feasible_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:26:26.219981+00:00
-- url     : https://prove2.me/submissions/43f27f1a-2e91-48da-9290-cfbab3563921

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

open DantzigSimplex.Technique in
theorem solution {m n : ℕ} (p : Problem m n)
    (q : PhaseIFrame p) (h : ∀ j, q.y0 j ≤ 0) :
    ∀ w : Fin n → ℝ, ¬ p.Feasible w := by
  intro w hfeas
  obtain ⟨hw0, hw⟩ := hfeas
  have hcle : ∑ j, w j * q.y0 j ≤ 0 :=
    Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw0 j) (h j))
  have key : ∀ a, p.rhs a = (∑ j, w j * q.y0 j) * p.rhs a
      + ∑ i ∈ q.S, (∑ j, w j * q.y i j) * p.col i a := by
    intro a
    have h1 : p.rhs a = ∑ j, w j * p.col j a := (congrFun hw a).symm
    have h2 : ∀ j, p.col j a = q.y0 j * p.rhs a + ∑ i ∈ q.S, q.y i j * p.col i a :=
      fun j => (congrFun (q.hcoord j) a).symm
    calc p.rhs a = ∑ j, w j * p.col j a := h1
      _ = ∑ j, w j * (q.y0 j * p.rhs a + ∑ i ∈ q.S, q.y i j * p.col i a) :=
          Finset.sum_congr rfl (fun j _ => by rw [h2 j])
      _ = (∑ j, w j * q.y0 j) * p.rhs a
          + ∑ i ∈ q.S, (∑ j, w j * q.y i j) * p.col i a := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          congr 1
          · exact Finset.sum_congr rfl (fun j _ => by ring)
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  let G : Option (Fin n) → ℝ := fun o =>
    Option.elim o (1 - ∑ j, w j * q.y0 j) (fun i => -(∑ j, w j * q.y i j))
  have hsum : ∑ x : {j // j ∈ insert none (q.S.image some)}, G x.1 • p.point x.1 = 0 := by
    rw [Finset.sum_coe_sort (insert none (q.S.image some)) (fun x => G x • p.point x)]
    rw [Finset.sum_insert (by simp), Finset.sum_image (by simp)]
    funext a
    have := key a
    simp [G, Problem.point, Finset.sum_apply]
    linarith
  have hli := Fintype.linearIndependent_iff.mp q.hind (fun x => G x.1) hsum
    ⟨none, Finset.mem_insert_self _ _⟩
  simp [G] at hli
  linarith
