-- Prove2me | solution 1 for CurveSymmetry.family_functionField_double_cover
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:56:52.243371+00:00
-- url     : https://prove2.me/submissions/34f79315-e9ba-4bae-8498-0960615d2e41

-- Solution generated from lean/FamilyFunctionField.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
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
variable {m : ℕ} {α : ℂ}
section FunctionField
variable [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyQuadraticRat_finrank :
    Module.finrank (RatFunc ℂ) (AdjoinRoot (familyQuadraticRat m α)) = 2 := by
  have hne : familyQuadraticRat m α ≠ 0 := by
    intro h
    have hd : (familyQuadraticRat m α).natDegree = 2 := by
      rw [familyQuadraticRat, natDegree_X_pow_sub_C]
    rw [h, natDegree_zero] at hd
    omega
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, familyQuadraticRat,
    natDegree_X_pow_sub_C]
end FunctionField
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial
variable {m : ℕ} {α : ℂ}
variable [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    (familyH m α).natDegree = 2 * m + 1 ∧ Squarefree (familyH m α) ∧
      Irreducible (familyQuadraticRat m α) ∧
      Module.finrank (RatFunc ℂ) (AdjoinRoot (familyQuadraticRat m α)) = 2 ∧
      familyRatFuncHom m α RatFunc.X = familyT m α ∧
      familyW m α ^ 2 = aeval (familyT m α) (familyH m α) ∧
      ∃ e : AdjoinRoot (familyQuadraticRat m α) ≃+* FamilyFunctionField m α,
        (∀ r, e (AdjoinRoot.of _ r) = familyRatFuncHom m α r) ∧
        e (AdjoinRoot.root _) = familyW m α :=
  ⟨familyH_natDegree_of hm.out ha.out, familyH_squarefree_of hm.out ha.out,
    familyQuadraticRat_irreducible_of hm.out ha.out, familyQuadraticRat_finrank,
    familyRatFuncHom_X, familyW_sq,
    RingEquiv.ofBijective (familyLift m α) ⟨familyLift_injective, familyLift_surjective⟩,
    fun r => familyLift_of r, familyLift_root⟩
end

#print axioms solution
