-- Prove2me | solution 1 for BudgetedAffine.Budget.coverCost_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:16:57.818111+00:00
-- url     : https://prove2.me/submissions/81659459-ddf3-4b41-b166-f29bfab45821

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model
import Definitions.Def_Polyhedron
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded

set_option autoImplicit false
open Matrix

theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (d : Fin n → ℝ)
    (h : Fin m → ℝ) (hd : 0 ≤ d) (hfin : BudgetedAffine.Budget.coverCost B d h ≠ ⊤) :
    ∃ y : Fin n → ℝ, BudgetedAffine.Budget.IsCoverOpt B d h y := by
  classical
  set A' : Matrix (Fin (m + n)) (Fin n) ℝ :=
    Matrix.of (fun k => Fin.addCases (motive := fun _ => Fin n → ℝ) (fun i => B i)
      (fun j => Pi.single j 1) k) with hA'
  set b' : Fin (m + n) → ℝ := Fin.addCases (motive := fun _ => ℝ) h (fun _ => 0) with hb'
  have hmem : ∀ y : Fin n → ℝ, y ∈ LinearOptimization.polyhedron A' b' ↔ 0 ≤ y ∧ h ≤ B *ᵥ y := by
    intro y
    unfold LinearOptimization.polyhedron
    simp only [Set.mem_setOf_eq]
    rw [Pi.le_def, Fin.forall_fin_add]
    simp only [hA', hb', Matrix.mulVec, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
      single_dotProduct, one_mul]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun j => h2 j, fun i => h1 i⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => h2 i, fun j => h1 j⟩
  have hne : (LinearOptimization.polyhedron A' b').Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hfin
    refine top_le_iff.1 (le_iInf₂ (fun y hy => ?_))
    have : y ∈ LinearOptimization.polyhedron A' b' := (hmem y).2 hy
    rw [hcon] at this
    exact absurd this (Set.notMem_empty y)
  rcases LinearOptimization.lp_attains_or_unbounded A' b' d hne with hbot | ⟨x, hxP, hxopt⟩
  · exfalso
    have h0 : (0 : EReal) ≤ LinearOptimization.lpValue d (LinearOptimization.polyhedron A' b') := by
      unfold LinearOptimization.lpValue
      refine le_iInf₂ (fun y hy => ?_)
      exact_mod_cast dotProduct_nonneg_of_nonneg hd ((hmem y).1 hy).1
    rw [hbot] at h0
    exact absurd h0 (by simp)
  · obtain ⟨hx0, hxh⟩ := (hmem x).1 hxP
    refine ⟨x, hx0, hxh, le_antisymm ?_ (iInf₂_le x ⟨hx0, hxh⟩)⟩
    refine le_iInf₂ (fun y hy => ?_)
    exact_mod_cast hxopt y ((hmem y).2 hy)
