-- Prove2me | solution 1 for CurveSymmetry.family_quadRing_points
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:32.073251+00:00
-- url     : https://prove2.me/submissions/a7facfd7-2a08-4ffc-9469-1a2d3780090b

-- Solution generated from lean/QuadraticRing.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Theorems.Thm_CurveSymmetry_quadRing_isMaximal_iff
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

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Function.Injective (quadRingMap (familyH m α)) ∧
      (∀ x : QuadField (familyH m α),
        IsIntegral ℂ[X] x ↔ ∃ y, quadRingMap (familyH m α) y = x) ∧
      ∀ 𝔪 : Ideal (QuadRing (familyH m α)), 𝔪.IsMaximal ↔
        ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c),
          𝔪 = RingHom.ker (quadEval (familyH m α) c d hd) :=
  ⟨quadRingMap_injective _ (familyH_squarefree_of hm ha).ne_zero,
    quadRingMap_range _ (familyH_squarefree_of hm ha),
    quadRing_isMaximal_iff _⟩
end

#print axioms solution
