-- Prove2me | solution 1 for D1Bound5.degenerate_pair_model
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T22:55:09.742393+00:00
-- url     : https://prove2.me/submissions/e1567d83-975b-4d1e-a6c7-21c1cffaec23

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DegeneratePairClassification_Definitions
import Theorems.Thm_D1Bound5_QuadInt_discriminant_le_four_bound
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_gaussian_degenerate_pair
import Theorems.Thm_D1Bound5_product_neg_one_norms

section
namespace D1Bound5
open QuadInt









/-- The only possible nonrational distinct product-minus-one pair lies
in the Eisenstein model. No smallness hypothesis is needed. -/
theorem _root_.solution {tau nu : ℤ}
    (htau : tau=0 ∨ tau=1) (hd : 0 < discriminant tau nu)
    (a b : QuadInt tau nu) (hne : a ≠ b) (hprod : a*b+1=0) :
    RationalUnitPair a b ∨ (tau=1 ∧ nu=1) := by
  obtain ⟨ha,hb⟩ := product_neg_one_norms hd a b hprod
  by_cases hia : a.im=0
  · by_cases hib : b.im=0
    · left
      have hra : a.re^2=1 := by simpa [norm_formula,hia] using ha
      have hfac : (a.re-1)*(a.re+1)=0 := by nlinarith only [hra]
      have hsign : a.re=1 ∨ a.re=-1 := by
        rcases mul_eq_zero.mp hfac with h | h
        · left; omega
        · right; omega
      rcases hsign with h | h
      · have he : a=1 := by apply QuadraticAlgebra.ext <;> simp [h,hia,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
        right
        refine ⟨he,?_⟩
        rw [he,one_mul] at hprod
        exact eq_neg_iff_add_eq_zero.mpr hprod
      · have he : a=-1 := by apply QuadraticAlgebra.ext <;> simp [h,hia,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
        left
        refine ⟨he,?_⟩
        rw [he,neg_one_mul] at hprod
        linear_combination -hprod
    · have hcut := discriminant_le_four_bound hd hb.le hib
      rcases htau with rfl | rfl
      · have hnu : nu=1 := by simp only [discriminant] at hd hcut; omega
        subst nu
        exact Or.inl (gaussian_degenerate_pair a b hne hprod)
      · have hnu : nu=1 := by simp only [discriminant] at hd hcut; omega
        exact Or.inr ⟨rfl,hnu⟩
  · have hcut := discriminant_le_four_bound hd ha.le hia
    rcases htau with rfl | rfl
    · have hnu : nu=1 := by simp only [discriminant] at hd hcut; omega
      subst nu
      exact Or.inl (gaussian_degenerate_pair a b hne hprod)
    · have hnu : nu=1 := by simp only [discriminant] at hd hcut; omega
      exact Or.inr ⟨rfl,hnu⟩







end D1Bound5
end
