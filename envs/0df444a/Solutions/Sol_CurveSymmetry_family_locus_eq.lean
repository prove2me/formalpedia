-- Prove2me | solution 1 for CurveSymmetry.family_locus_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:55.689496+00:00
-- url     : https://prove2.me/submissions/6aa2d34f-74e1-439a-8b84-50ff3e698b3e

-- Solution generated from lean/PaperBounds.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
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
lemma mul_star_norm_sq (z : ℂ) : z * star z = (‖z‖ : ℂ) ^ 2 := by
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma eval_familyPolynomial (m : ℕ) (α z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (familyPolynomial m α) =
      z ^ m * (α + z * star z) + star (z ^ m * (α + z * star z)) := by
  simp only [familyPolynomial, map_add, map_mul, map_pow, eval_C, eval_X,
    Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide,
    star_mul, star_pow, star_add, star_star]
  ring
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution (m : ℕ) (α : ℂ) :
    realLocus (familyPolynomial m α) = extremalCurve m α := by
  ext z
  change MvPolynomial.eval _ (familyPolynomial m α) = 0 ↔ _
  rw [eval_familyPolynomial, mul_star_norm_sq, add_comm α]
  have he : z ^ m * ((‖z‖ : ℂ) ^ 2 + α) + star (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)) =
      ((2 * (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re : ℝ) : ℂ) :=
    Complex.add_conj _
  change _ + star _ = 0 ↔ (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0
  rw [he, Complex.ofReal_eq_zero]
  simp
end

#print axioms solution
