-- Prove2me | solution 1 for CurveSymmetry.quadEval_ker_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:20.95009+00:00
-- url     : https://prove2.me/submissions/1b40b5e6-0fff-4dd1-86cd-982ae25eb208

-- Solution generated from lean/QuadraticRing.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
section
variable (h : ℂ[X])
lemma quadEval_root (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    quadEval h c d hd (AdjoinRoot.root _) = d :=
  AdjoinRoot.lift_root _
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable (h : ℂ[X])
theorem solution {c d c' d' : ℂ} (hd : d ^ 2 = h.eval c) (hd' : d' ^ 2 = h.eval c')
    (he : RingHom.ker (quadEval h c d hd) = RingHom.ker (quadEval h c' d' hd')) :
    c = c' ∧ d = d' := by
  have hX : AdjoinRoot.of (quadPoly h) (X - C c) ∈ RingHom.ker (quadEval h c d hd) := by
    rw [RingHom.mem_ker, quadEval_of, eval_sub, eval_X, eval_C, sub_self]
  have hW : AdjoinRoot.root (quadPoly h) - AdjoinRoot.of _ (C d) ∈
      RingHom.ker (quadEval h c d hd) := by
    rw [RingHom.mem_ker, map_sub, quadEval_root, quadEval_of, eval_C, sub_self]
  rw [he, RingHom.mem_ker, quadEval_of, eval_sub, eval_X, eval_C, sub_eq_zero] at hX
  rw [he, RingHom.mem_ker, map_sub, quadEval_root, quadEval_of, eval_C, sub_eq_zero] at hW
  exact ⟨hX.symm, hW.symm⟩
end

#print axioms solution
