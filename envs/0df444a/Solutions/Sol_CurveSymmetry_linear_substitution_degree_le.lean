-- Prove2me | solution 1 for CurveSymmetry.linear_substitution_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:12.28712+00:00
-- url     : https://prove2.me/submissions/01d600e4-68e4-4c73-8b3a-b07d6590d225

-- Solution generated from lean/CartesianCoordinates.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma totalDegree_sum_le {ι : Type*} (s : Finset ι) (F : ι → BPoly) (d : ℕ)
    (h : ∀ i ∈ s, (F i).totalDegree ≤ d) : (∑ i ∈ s, F i).totalDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (totalDegree_add _ _).trans (max_le (h a (by simp))
        (ih (fun i hi => h i (by simp [hi]))))
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution (v : Fin 2 → BPoly) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (P : BPoly) : (eval₂Hom C v P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_sum_le
  intro s hs
  rw [eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  have h0 := (totalDegree_pow (v 0) (s 0)).trans (Nat.mul_le_mul_left (s 0) (hv 0))
  have h1 := (totalDegree_pow (v 1) (s 1)).trans (Nat.mul_le_mul_left (s 1) (hv 1))
  have hm := totalDegree_mul (v 0 ^ s 0) (v 1 ^ s 1)
  have hc := totalDegree_mul (C (P.coeff s) : BPoly) (v 0 ^ s 0 * v 1 ^ s 1)
  simp only [totalDegree_C, zero_add, Nat.mul_one] at h0 h1 hc
  have hd := support_degree hs
  omega
end

#print axioms solution
