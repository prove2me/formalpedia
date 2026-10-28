-- Prove2me | solution 1 for D1Bound5.IsD1.one_three_small_third_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:37:25.120862+00:00
-- url     : https://prove2.me/submissions/3f1c2e28-16c6-41a0-8510-75beeb80f136

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_IsD1_one_three_all_positive_integers
import Theorems.Thm_D1Bound5_QuadInt_norm_formula
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_full_ring_positive_integer_square
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField Classical
open Module

namespace D1Bound5

/-- The only integer strictly between 3 and 15 whose successor is a
square is 8. The additional 3s+1 square condition is unnecessary here. -/
theorem integer_one_three_third_eq_eight (s r : ℤ)
    (hlo : 3 < s) (hhi : s < 15) (hr : r*r = s+1) : s = 8 := by
  have hrlo : -3 ≤ r := by nlinarith [sq_nonneg (r+3)]
  have hrhi : r ≤ 3 := by nlinarith [sq_nonneg (r-3)]
  interval_cases r <;> nlinarith

/-- In any actual full ring, a D(1)-set of cardinality at least five
containing 1 and 3 has exactly the third candidate 8 below modulus 15.
The accepted negative-extension theorem supplies positivity and rationality. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {A : Finset (𝓞 K)} (hA : IsD1 A)
    (h1 : (1 : 𝓞 K) ∈ A) (h3 : (3 : 𝓞 K) ∈ A) (hcard : 4 < A.card)
    (z : 𝓞 K) (hz : z ∈ A) (hz1 : z ≠ 1) (hz3 : z ≠ 3)
    (hlo : 9 ≤ ‖phi (z : K)‖^2) (hhi : ‖phi (z : K)‖^2 < 225) : z = 8 := by
  classical
  obtain ⟨s,hs,rfl⟩ := hA.one_three_all_positive_integers hK h1 h3 hcard z hz
  obtain ⟨tau,nu,_,_,⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  have hnorm : ‖phi ((s : 𝓞 K) : K)‖^2 = (s : ℝ)^2 := by
    have h := norm_sq_full_ring_equiv e phi (s : QuadInt tau nu)
    simpa [QuadInt.norm_formula] using h
  rw [hnorm] at hlo hhi
  have hslo : (9 : ℤ) ≤ s^2 := by exact_mod_cast hlo
  have hshi : s^2 < 225 := by exact_mod_cast hhi
  have hs3 : s ≠ 3 := by intro h; apply hz3; simp [h]
  have hsge3 : 3 ≤ s := by nlinarith
  have hslo' : 3 < s := by omega
  have hshi' : s < 15 := by nlinarith
  obtain ⟨r,hr⟩ := full_ring_positive_integer_square hK (m := s+1) (by omega)
    (by simpa using hA.2 1 h1 (s : 𝓞 K) hz (Ne.symm hz1))
  have heq := integer_one_three_third_eq_eight s r hslo' hshi' (by nlinarith [hr])
  simp [heq]



end D1Bound5
end
