-- Prove2me | solution 1 for CurveSymmetry.opposite_symmetry_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:02:51.681633+00:00
-- url     : https://prove2.me/submissions/5026da9b-2e74-4c9c-b47f-00c9972b2958

-- Solution generated from lean/IsometrySign.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_opposite_symmetry_no_glide
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

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {a b : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) : a * star (b / 2) + b = b / 2 := by
  have hg := opposite_symmetry_no_glide hP hd hne h
  have hs : star (b / 2) = star b / 2 := by simp
  rw [hs]
  linear_combination hg / 2
end

#print axioms solution
