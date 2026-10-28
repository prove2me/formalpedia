-- Prove2me | solution 1 for D1Bound5.coherent_two_three_forms_not_both_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:52.654327+00:00
-- url     : https://prove2.me/submissions/43ad1582-5a28-42ec-a6b8-f3042b38a3b3

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions
import Theorems.Thm_D1Bound5_coherent_elementary_norm_bounds
import Theorems.Thm_D1Bound5_coherent_four_vanishing_identity_norm_le
import Theorems.Thm_D1Bound5_coherent_four_vanishing_size_contradiction
import Theorems.Thm_D1Bound5_coherent_two_three_forms_vanishing_identity

section
open Finset

namespace D1Bound5







/-- The two coherent polynomial-weight forms cannot both vanish under
the four-anchor size condition.  Arbitrary square-root signs are
allowed, provided the two forms use the same roots on their overlap. -/
theorem _root_.solution
    (a R : Fin 4 → ℂ) (hinj : Function.Injective a) (p q z : ℂ)
    (hz : z^2 = p*q+1) (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (hA : 1 ≤ ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hBS : ‖a 1‖ ≤ ‖a 2‖) (hST : ‖a 2‖ ≤ ‖a 3‖)
    (hTP : ‖a 3‖ ≤ ‖p‖) (hPQ : ‖p‖ ≤ ‖q‖)
    (hsize : 32*‖a 1‖*‖a 2‖*‖a 3‖/‖a 0‖^3 ≤ ‖p‖^2) :
    (-(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*z +
      a 0*(a 1-a 2)*R 0 - a 1*(a 0-a 2)*R 1 + a 2*(a 0-a 1)*R 2 ≠ 0) ∨
    (-(a 0-a 1)*(a 0-a 3)*(a 1-a 3)*z +
      a 0*(a 1-a 3)*R 0 - a 1*(a 0-a 3)*R 1 + a 3*(a 0-a 1)*R 3 ≠ 0) := by
  by_contra hzero
  push_neg at hzero
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    fin_cases i
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 0‖)
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 1‖)
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 2‖)
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 3‖)
  have hid := coherent_two_three_forms_vanishing_identity a R hinj ha p q z hz hR hzero.1 hzero.2
  obtain ⟨he2, he3, he4⟩ := coherent_elementary_norm_bounds a hAB hBS hST
  have hupper := coherent_four_vanishing_identity_norm_le
    (coherentElementary2 a) (coherentElementary3 a) (coherentElementary4 a) p q
    ‖a 0‖ ‖a 1‖ ‖a 2‖ ‖a 3‖ hA hAB hBS hST he2 he3 he4 hid
  have hlower : ‖p‖*‖q‖-1 ≤ ‖p*q+1‖ := by
    have h := norm_sub_le (p*q+1) (1 : ℂ)
    simp only [add_sub_cancel_right, norm_mul, norm_one] at h
    linarith
  exact coherent_four_vanishing_size_contradiction
    ‖a 0‖ ‖a 1‖ ‖a 2‖ ‖a 3‖ ‖p‖ ‖q‖ ‖p*q+1‖
    hA hAB hBS hST hTP hPQ hsize hupper hlower







end D1Bound5
end
