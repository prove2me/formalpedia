-- Prove2me | solution 1 for ErlerGross.integral_cosh_div_cosh_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T12:47:38.321229+00:00
-- url     : https://prove2.me/submissions/f690933e-02ff-4e11-b301-b2b48fc8bd9a

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_integral_cosh_div_cosh_near_zero_integrable
import Theorems.Thm_ErlerGross_integral_cosh_div_cosh_tail_integrable

open Real Filter Topology MeasureTheory

theorem solution (a b : Complex) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : Real => Complex.cosh (a * x) / Complex.cosh (b * x))
      (Set.Ioi 0) := by
  let f : Real → Complex := fun x => Complex.cosh (a * x) / Complex.cosh (b * x)
  have hnear : IntegrableOn f (Set.Ioo 0 1) := by
    simpa [f] using ErlerGross.integral_cosh_div_cosh_near_zero_integrable a b hab
  have htail : IntegrableOn f (Set.Ioi 1) := by
    simpa [f] using ErlerGross.integral_cosh_div_cosh_tail_integrable a b hab
  have hone : IntegrableOn f ({1} : Set Real) := by
    exact integrableOn_singleton (by simp) (by simp)
  have hdecomp : Set.Ioi (0 : Real) = Set.Ioo 0 1 ∪ (Set.Ioi 1 ∪ {1}) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_cases hlt : x < 1
      · exact Or.inl ⟨hx, hlt⟩
      · by_cases heq : x = 1
        · exact Or.inr (Or.inr heq)
        · exact Or.inr (Or.inl (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)))
    · rintro (⟨hx, _⟩ | (hx | rfl))
      · exact hx
      · linarith
      · norm_num
  rw [hdecomp]
  exact hnear.union (htail.union hone)
