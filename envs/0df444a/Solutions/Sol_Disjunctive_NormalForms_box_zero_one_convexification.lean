-- Prove2me | solution 1 for Disjunctive.NormalForms.box_zero_one_convexification
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:52:06.189869+00:00
-- url     : https://prove2.me/submissions/3b59714f-8995-467e-a14e-741d13491b58

import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

set_option autoImplicit false

namespace P127c79db

open Set

lemma box_eq (n : ℕ) :
    {x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1)} = Set.Icc (0 : Fin n → ℝ) 1 := by
  ext x
  simp only [Set.mem_setOf_eq, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply, forall_and]

lemma ext_box (n : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ (Set.Icc (0 : Fin n → ℝ) 1).extremePoints ℝ) (i : Fin n) :
    x i = 0 ∨ x i = 1 := by
  have h : (Set.Icc (0 : Fin n → ℝ) 1) = Set.univ.pi (fun _ : Fin n => Set.Icc (0:ℝ) 1) := by
    rw [Set.pi_univ_Icc]; rfl
  rw [h, extremePoints_pi] at hx
  have := hx i (Set.mem_univ i)
  rw [Set.extremePoints_Icc zero_le_one] at this
  simpa using this

lemma closure_hull_eq (n : ℕ) (T : Set (Fin n → ℝ))
    (h1 : (Set.Icc (0 : Fin n → ℝ) 1).extremePoints ℝ ⊆ T)
    (h2 : T ⊆ Set.Icc (0 : Fin n → ℝ) 1) :
    closure (convexHull ℝ T) = Set.Icc (0 : Fin n → ℝ) 1 := by
  apply le_antisymm
  · exact closure_minimal (convexHull_min h2 (convex_Icc _ _)) isClosed_Icc
  · conv_lhs => rw [← closure_convexHull_extremePoints (isCompact_Icc) (convex_Icc (0 : Fin n → ℝ) 1)]
    exact closure_mono (convexHull_mono h1)

end P127c79db

theorem solution {n : ℕ} :
    closure (convexHull ℝ
        (⋂ j : Fin n, {x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1)} ∩
          ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}))) =
      ⋂ j : Fin n, closure (convexHull ℝ
        ({x : Fin n → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1)} ∩
          ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}))) := by
  rw [P127c79db.box_eq n]
  have hext : ∀ x ∈ (Set.Icc (0 : Fin n → ℝ) 1).extremePoints ℝ, ∀ j : Fin n,
      x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∩
        ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}) := by
    intro x hx j
    refine ⟨hx.1, ?_⟩
    rcases P127c79db.ext_box n x hx j with h | h
    · left; show x j ≤ 0; rw [h]
    · right; show 1 ≤ x j; rw [h]
  have hR : ∀ j : Fin n, closure (convexHull ℝ
        (Set.Icc (0 : Fin n → ℝ) 1 ∩
          ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}))) = Set.Icc (0 : Fin n → ℝ) 1 := by
    intro j
    exact P127c79db.closure_hull_eq n _ (fun x hx => hext x hx j) Set.inter_subset_left
  have hL : closure (convexHull ℝ
        (⋂ j : Fin n, Set.Icc (0 : Fin n → ℝ) 1 ∩
          ({x : Fin n → ℝ | x j ≤ 0} ∪ {x : Fin n → ℝ | 1 ≤ x j}))) = Set.Icc (0 : Fin n → ℝ) 1 := by
    apply P127c79db.closure_hull_eq n
    · intro x hx
      exact Set.mem_iInter.2 (fun j => hext x hx j)
    · intro x hx
      rw [Set.mem_iInter] at hx
      constructor
      · intro i; exact (hx i).1.1 i
      · intro i; exact (hx i).1.2 i
  rw [hL]
  simp_rw [hR]
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro h j; exact h
  · intro h
    constructor
    · intro i; exact (h i).1 i
    · intro i; exact (h i).2 i
