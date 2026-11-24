-- Prove2me | solution 1 for ChaChaTree.DynOpt.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T19:39:53.4468+00:00
-- url     : https://prove2.me/submissions/ba084f69-778f-45c1-afe8-1dff1a7653e0

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles

set_option autoImplicit false

namespace ChaChaLemma12Aux
open ChaChaTree.DynOpt

/-- If `r₁` contains no corner of `r₂`, then `r₂` contains no corner of `r₁`, unless the two
input-free rectangles share a defining point. -/
theorem corner_symm (P : Finset (ℕ × ℕ)) (r₁ r₂ : Rect)
    (h₁ : IsRectOn P r₁ ∧ InputFree P r₁) (h₂ : IsRectOn P r₂ ∧ InputFree P r₂)
    (hns : ¬ ShareDefiningPoint r₁ r₂)
    (hall : ∀ c ∈ corners r₂, ¬ RContains r₁ c) :
    ∀ c ∈ corners r₁, ¬ RContains r₂ c := by
  rcases r₁ with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩
  rcases r₂ with ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩
  obtain ⟨⟨hp1, hq1, hlt1, hne1⟩, hif1⟩ := h₁
  obtain ⟨⟨hp2, hq2, hlt2, hne2⟩, hif2⟩ := h₂
  have i1 := hif2 _ hp1
  have i2 := hif2 _ hq1
  have i3 := hif1 _ hp2
  have i4 := hif1 _ hq2
  simp only [RContains, Prod.mk.injEq] at i1 i2 i3 i4
  simp only [ShareDefiningPoint, Prod.mk.injEq] at hns
  simp only [corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, RContains] at hall ⊢
  simp only at hlt1 hne1 hlt2 hne2 i1 i2 i3 i4 hall ⊢
  rcases Nat.lt_or_gt_of_ne hne1 with o1 | o1 <;> rcases Nat.lt_or_gt_of_ne hne2 with o2 | o2 <;>
    simp only [min_eq_left o1.le, max_eq_right o1.le, min_eq_right o1.le, max_eq_left o1.le,
      min_eq_left o2.le, max_eq_right o2.le, min_eq_right o2.le, max_eq_left o2.le]
      at i1 i2 i3 i4 hall ⊢ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hc <;> omega

/-- A right and a left input-free rectangle without a shared defining point: the left one
contains no corner of the right one. -/
theorem right_left (P : Finset (ℕ × ℕ)) (r₁ r₂ : Rect)
    (h₁ : IsRectOn P r₁ ∧ InputFree P r₁) (h₂ : IsRectOn P r₂ ∧ InputFree P r₂)
    (hns : ¬ ShareDefiningPoint r₁ r₂) (hr : IsRightRect r₁) (hl : IsLeftRect r₂) :
    ∀ c ∈ corners r₁, ¬ RContains r₂ c := by
  rcases r₁ with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩
  rcases r₂ with ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩
  obtain ⟨⟨hp1, hq1, hlt1, hne1⟩, hif1⟩ := h₁
  obtain ⟨⟨hp2, hq2, hlt2, hne2⟩, hif2⟩ := h₂
  have i1 := hif2 _ hp1
  have i2 := hif2 _ hq1
  have i3 := hif1 _ hp2
  have i4 := hif1 _ hq2
  simp only [RContains, Prod.mk.injEq] at i1 i2 i3 i4
  simp only [ShareDefiningPoint, Prod.mk.injEq] at hns
  simp only [corners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, RContains]
  simp only [IsRightRect, IsLeftRect] at hr hl
  simp only at hlt1 hne1 hlt2 hne2 i1 i2 i3 i4 hr hl ⊢
  omega

theorem share_symm (r₁ r₂ : Rect) : ShareDefiningPoint r₁ r₂ ↔ ShareDefiningPoint r₂ r₁ := by
  unfold ShareDefiningPoint
  constructor <;> rintro (h | h | h | h) <;> simp [h]

theorem pair (P : Finset (ℕ × ℕ)) (r₁ r₂ : Rect)
    (h₁ : IsRectOn P r₁ ∧ InputFree P r₁) (h₂ : IsRectOn P r₂ ∧ InputFree P r₂)
    (h : ShareDefiningPoint r₁ r₂ ∨ (IsRightRect r₁ ∧ IsLeftRect r₂) ∨
      (IsLeftRect r₁ ∧ IsRightRect r₂) ∨ (∀ c ∈ corners r₂, ¬ RContains r₁ c) ∨
      (∀ c ∈ corners r₁, ¬ RContains r₂ c)) :
    ShareDefiningPoint r₁ r₂ ∨ NoCornerContained r₁ r₂ := by
  by_cases hs : ShareDefiningPoint r₁ r₂
  · exact Or.inl hs
  right
  have hs' : ¬ ShareDefiningPoint r₂ r₁ := fun h' => hs ((share_symm _ _).2 h')
  rcases h with h | ⟨hr, hl⟩ | ⟨hl, hr⟩ | h | h
  · exact absurd h hs
  · have h2 := right_left P r₁ r₂ h₁ h₂ hs hr hl
    exact ⟨corner_symm P r₂ r₁ h₂ h₁ hs' h2, h2⟩
  · have h2 := right_left P r₂ r₁ h₂ h₁ hs' hr hl
    exact ⟨h2, corner_symm P r₁ r₂ h₁ h₂ hs h2⟩
  · exact ⟨h, corner_symm P r₁ r₂ h₁ h₂ hs h⟩
  · exact ⟨corner_symm P r₂ r₁ h₂ h₁ hs' h, h⟩

end ChaChaLemma12Aux

open ChaChaTree.DynOpt ChaChaLemma12Aux

theorem solution (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (r₁ r₂ : Rect)
    (h₁ : IsRectOn P r₁ ∧ InputFree P r₁) (h₂ : IsRectOn P r₂ ∧ InputFree P r₂)
    (h : ShareDefiningPoint r₁ r₂ ∨ (IsRightRect r₁ ∧ IsLeftRect r₂) ∨
      (IsLeftRect r₁ ∧ IsRightRect r₂) ∨ (∀ c ∈ corners r₂, ¬ RContains r₁ c) ∨
      (∀ c ∈ corners r₁, ¬ RContains r₂ c)) :
    IsStrictlyIndependent P {r₁, r₂} := by
  have h12 := pair P r₁ r₂ h₁ h₂ h
  have h21 : ShareDefiningPoint r₂ r₁ ∨ NoCornerContained r₂ r₁ := by
    rcases h12 with h | h
    · exact Or.inl ((share_symm _ _).1 h)
    · exact Or.inr ⟨h.2, h.1⟩
  refine ⟨fun r hr => ?_, fun a ha b hb hab => ?_⟩
  · rcases Finset.mem_insert.1 hr with rfl | hr
    · exact h₁
    · rw [Finset.mem_singleton.1 hr]; exact h₂
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at hab ⊢
    · exact absurd rfl hab
    · exact h12
    · exact h21
    · exact absurd rfl hab
