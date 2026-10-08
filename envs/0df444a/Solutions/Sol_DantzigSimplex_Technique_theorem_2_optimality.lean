-- Prove2me | solution 1 for DantzigSimplex.Technique.theorem_2_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:55:43.169987+00:00
-- url     : https://prove2.me/submissions/b1b997d6-9165-4cdd-8e9e-764e3613dd6d

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

set_option autoImplicit false

namespace DantzigSimplex.Technique.Aux81490b9d

open DantzigSimplex.Technique

theorem basic_coord {m n : ℕ} (p : Problem m n) (s : PhaseIIState p)
    (v : Fin n → ℝ) (hv : p.Feasible v) :
    ∀ i ∈ s.frame.B, ∑ j, v j * s.frame.x i j = s.weight i := by
  classical
  set B := s.frame.B with hB
  set y : Fin n → ℝ := fun i => ∑ j, v j * s.frame.x i j with hy
  -- the combination over B with coefficients y gives rhs
  have h1 : ∀ a, ∑ i ∈ B, y i * p.col i a = p.rhs a := by
    intro a
    have hc : ∀ j, ∑ i ∈ B, s.frame.x i j * p.col i a = p.col j a := by
      intro j
      have := congrFun (s.frame.hcoord j) a
      simpa using this
    calc ∑ i ∈ B, y i * p.col i a
        = ∑ i ∈ B, ∑ j, v j * (s.frame.x i j * p.col i a) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hy, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
      _ = ∑ j, v j * ∑ i ∈ B, s.frame.x i j * p.col i a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ j, v j * p.col j a := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hc j]
      _ = p.rhs a := by
          have := congrFun hv.2 a
          simpa [Problem.combine] using this
  have h2 : ∀ a, ∑ i ∈ B, s.weight i * p.col i a = p.rhs a := by
    intro a
    have hsub : ∑ i ∈ B, s.weight i * p.col i a = ∑ i, s.weight i * p.col i a := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [s.hzero i hi, zero_mul]
    rw [hsub]
    have := congrFun s.hfeasible.2 a
    simpa [Problem.combine] using this
  have hli := s.frame.hind
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun a => y a.1 - s.weight a.1) (by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have e : ∑ x : {j // j ∈ B}, (y x.1 - s.weight x.1) * p.col x.1 a
        = ∑ i ∈ B, (y i - s.weight i) * p.col i a :=
      Finset.sum_coe_sort B (fun i => (y i - s.weight i) * p.col i a)
    rw [e]
    simp only [sub_mul, Finset.sum_sub_distrib, h1 a, h2 a, sub_self])
  intro i hi
  have := key ⟨i, hi⟩
  simp only at this
  have : y i = s.weight i := by linarith
  simpa [hy] using this

end DantzigSimplex.Technique.Aux81490b9d

open DantzigSimplex.Technique in
theorem solution {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (s : PhaseIIState p) (h : ∀ j, p.cost j ≤ s.frame.z j) :
    p.MaximumFeasible s.weight := by
  classical
  refine ⟨s.hfeasible, fun v hv => ?_⟩
  have hc := DantzigSimplex.Technique.Aux81490b9d.basic_coord p s v hv
  unfold Problem.objective
  calc ∑ j, v j * p.cost j
      ≤ ∑ j, v j * s.frame.z j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (h j) (hv.1 j)
    _ = ∑ i ∈ s.frame.B, (∑ j, v j * s.frame.x i j) * p.cost i := by
        simp only [PhaseIIFrame.z, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
    _ = ∑ i ∈ s.frame.B, s.weight i * p.cost i := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hc i hi]
    _ = ∑ j, s.weight j * p.cost j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        rw [s.hzero i hi, zero_mul]
