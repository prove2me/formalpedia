-- Prove2me | solution 1 for CurveSymmetry.opposite_symmetry_no_glide
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:01:21.698678+00:00
-- url     : https://prove2.me/submissions/dee1c032-4828-44c9-8b9d-1ab41df17f17

-- Solution generated from lean/IsometrySign.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Theorems.Thm_CurveSymmetry_no_translation_symmetry
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
lemma mul_star_eq_one_of_norm {a : ℂ} (ha : ‖a‖ = 1) : a * star a = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  change a * (starRingEnd ℂ) a = 1
  rw [← Complex.inv_eq_conj ha, mul_inv_cancel₀ hn]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open MvPolynomial
theorem solution {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {a b : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) : a * star b + b = 0 := by
  have ha := mul_star_eq_one_of_norm h.1
  apply no_translation_symmetry hP hd hne
  intro z hz
  have h2 := (h.2 (a * star z + b)).mpr ((h.2 z).mpr hz)
  have he : a * star (a * star z + b) + b = z + (a * star b + b) := by
    simp only [star_add, star_mul, star_star]
    linear_combination z * ha
  rwa [he] at h2
end

#print axioms solution
