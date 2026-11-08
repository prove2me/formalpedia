-- Prove2me | solution 1 for CombOpt.MatroidIntersectionPolytope.proposition_8_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:02:24.345269+00:00
-- url     : https://prove2.me/submissions/dad7ad62-625c-41bd-b058-238524018f27

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_coverSum
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsOptimal82
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsOptimal88

open CombOpt.MatroidIntersectionPolytope in
theorem solution {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S)
    (c : S → ℝ) (ybar₁ ybar₂ : Finset S → ℝ) (hopt : IsOptimal88 M₁ M₂ c (ybar₁, ybar₂)) :
    (IsOptimal82 M₁ (coverSum ybar₁) ybar₁ ∧ IsOptimal82 M₂ (c - coverSum ybar₁) ybar₂) ∧
      ∀ y₁ y₂ : Finset S → ℝ, IsOptimal82 M₁ (coverSum ybar₁) y₁ →
        IsOptimal82 M₂ (c - coverSum ybar₁) y₂ → IsOptimal88 M₁ M₂ c (y₁, y₂) := by
  obtain ⟨⟨hy1, hy2, hcov⟩, hmin⟩ := hopt
  change ∀ A, 0 ≤ ybar₁ A at hy1
  change ∀ A, 0 ≤ ybar₂ A at hy2
  change ∀ e, c e ≤ coverSum ybar₁ e + coverSum ybar₂ e at hcov
  change ∀ y' ∈ dualFeasible88 c, ∑ A, ((rank M₁ A : ℝ) * ybar₁ A + (rank M₂ A : ℝ) * ybar₂ A) ≤
        ∑ A, ((rank M₁ A : ℝ) * y'.1 A + (rank M₂ A : ℝ) * y'.2 A) at hmin
  have f1 : ybar₁ ∈ dualFeasible82 (coverSum ybar₁) := ⟨hy1, fun e => le_refl _⟩
  have f2 : ybar₂ ∈ dualFeasible82 (c - coverSum ybar₁) :=
    ⟨hy2, fun e => by simp only [Pi.sub_apply]; linarith [hcov e]⟩
  refine ⟨⟨⟨f1, fun y' hy' => ?_⟩, ⟨f2, fun y' hy' => ?_⟩⟩, fun y₁ y₂ h1 h2 => ?_⟩
  · have hf : (y', ybar₂) ∈ dualFeasible88 c :=
      ⟨hy'.1, hy2, fun e => by
        show c e ≤ coverSum y' e + coverSum ybar₂ e; linarith [hcov e, hy'.2 e]⟩
    have := hmin _ hf
    simp only [Finset.sum_add_distrib] at this
    linarith
  · have hf : (ybar₁, y') ∈ dualFeasible88 c :=
      ⟨hy1, hy'.1, fun e => by
        have := hy'.2 e
        simp only [Pi.sub_apply] at this
        show c e ≤ coverSum ybar₁ e + coverSum y' e; linarith⟩
    have := hmin _ hf
    simp only [Finset.sum_add_distrib] at this
    linarith
  · obtain ⟨⟨g1, g1c⟩, o1⟩ := h1
    obtain ⟨⟨g2, g2c⟩, o2⟩ := h2
    have hf : (y₁, y₂) ∈ dualFeasible88 c :=
      ⟨g1, g2, fun e => by
        have a1 := g1c e
        have a2 := g2c e
        simp only [Pi.sub_apply] at a2
        show c e ≤ coverSum y₁ e + coverSum y₂ e; linarith⟩
    refine ⟨hf, fun y' hy' => ?_⟩
    have b1 := o1 ybar₁ f1
    have b2 := o2 ybar₂ f2
    have b3 := hmin y' hy'
    simp only [Finset.sum_add_distrib] at b3 ⊢
    linarith
