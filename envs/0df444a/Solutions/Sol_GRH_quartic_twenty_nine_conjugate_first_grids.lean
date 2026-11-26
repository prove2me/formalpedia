-- Prove2me | solution 1 for GRH.quartic_twenty_nine_conjugate_first_grids
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:48:07.449384+00:00
-- url     : https://prove2.me/submissions/b1077d6b-ff3f-4f2d-a91c-4b08031c7803

import Theorems.Thm_GRH_dirichlet_quartic_twenty_nine_first_rectangle
import Theorems.Thm_GRH_dirichlet_grid_inverse_and_reflected_cells
import Theorems.Thm_GRH_dirichlet_rectangle_nonzero_iff_finite_grid
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open GRH.DirichletGrid Complex
open scoped ComplexConjugate

/-- Each quartic character at level 29 passes the finite test throughout each
of the three certified closed rectangles and their subrectangles. -/
theorem solution (χ : DirichletCharacter ℂ 29) (hv : χ 2=Complex.I ∨ χ 2= -Complex.I)
    (a b H : ℝ) (hab : a≤b) (hb : b≤7/8) (hH : 0≤H)
    (region : (3/4≤a ∧ H≤1) ∨ (5/6≤a ∧ H≤3/2) ∨ (6/7≤a ∧ H≤7/4)) :
    ∃ m : ℕ, Passes χ a b H m := by
  have direct (η : DirichletCharacter ℂ 29) (he : η 2=I) : ∃ m : ℕ, Passes η a b H m := by
    have hne : η≠1 := by
      intro e
      rw [e,MulChar.one_apply (x:=(2:ZMod 29)) ((ZMod.isUnit_iff_coprime 2 29).2 (by decide))] at he
      simpa using congrArg Complex.im he
    have hal : (1/2:ℝ)≤a := by rcases region with hl|hl|hl <;> linarith [hl.1]
    apply (GRH.dirichlet_rectangle_nonzero_iff_finite_grid 29 η hne a b H hal hab (by linarith) hH).1
    intro z hz
    apply GRH.dirichlet_quartic_twenty_nine_first_rectangle η he z (hz.1.2.trans hb)
    have him := abs_le.mpr hz.2
    rcases region with h|h|h
    · exact Or.inl ⟨h.1.trans hz.1.1,him.trans h.2⟩
    · exact Or.inr (Or.inl ⟨h.1.trans hz.1.1,him.trans h.2⟩)
    · exact Or.inr (Or.inr ⟨h.1.trans hz.1.1,him.trans h.2⟩)
  rcases hv with h|h
  · exact direct χ h
  · have e : χ⁻¹ 2=I := by rw [← MulChar.star_apply'];change conj (χ 2)=I;simp [h]
    obtain ⟨m,hm⟩ := direct χ⁻¹ e
    exact ⟨m,(GRH.dirichlet_grid_inverse_and_reflected_cells χ a b H m).1.1 hm⟩
